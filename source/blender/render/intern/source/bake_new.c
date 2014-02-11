/*
 * ***** BEGIN GPL LICENSE BLOCK *****
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA.
 *
 * Contributors: 2004/2005/2006 Blender Foundation, full recode
 * Contributors: Vertex color baking, Copyright 2011 AutoCRC
 *
 * ***** END GPL LICENSE BLOCK *****
 */

/** \file blender/render/intern/source/bake.c
 *  \ingroup render
 */


/* system includes */
#include <stdio.h>
#include <string.h>

/* External modules: */
#include "MEM_guardedalloc.h"

#include "BLI_math.h"
#include "BLI_blenlib.h"
#include "BLI_threads.h"
#include "BLI_utildefines.h"

#include "DNA_image_types.h"
#include "DNA_material_types.h"
#include "DNA_mesh_types.h"
#include "DNA_meshdata_types.h"

#include "BKE_customdata.h"
#include "BKE_cdderivedmesh.h"
#include "BKE_mesh.h"
#include "BKE_global.h"
#include "BKE_image.h"
#include "BKE_main.h"
#include "BKE_node.h"
#include "BKE_scene.h"
#include "BKE_library.h"

#include "BKE_bvhutils.h"
#include "BKE_DerivedMesh.h"

#include "IMB_imbuf_types.h"
#include "IMB_imbuf.h"
#include "IMB_colormanagement.h"

#include "RE_bake.h"

/* local include */
#include "rayintersection.h"
#include "rayobject.h"
#include "render_types.h"
#include "renderdatabase.h"
#include "shading.h"
#include "zbuf.h"

#include "PIL_time.h"

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */
/* defined in pipeline.c, is hardcopy of active dynamic allocated Render */
/* only to be used here in this file, it's for speed */
extern struct Render R;
/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */


typedef struct BakeData {
	BakePixel *pixel_array;
	int width;
	int primitive_id;
	ZSpan zspan;
} BakeData;

/* ************************* bake ************************ */
static void store_bake_pixel(void *handle, int x, int y, float u, float v)
{
	BakeData *bd = (BakeData *)handle;
	BakePixel *pixel_array = bd->pixel_array;
	const int width = bd->width;
	const int i = y * width + x;

	pixel_array[i].primitive_id = bd->primitive_id;
	pixel_array[i].u = u;
	pixel_array[i].v = v;

	pixel_array[i].dudx =
	pixel_array[i].dudy =
	pixel_array[i].dvdx =
	pixel_array[i].dvdy =
	0.f;
}

void RE_bake_margin(BakePixel pixel_array[], ImBuf *ibuf, const int margin, const int width, const int height)
{
	char *mask_buffer = NULL;
	const int num_pixels = width * height;
	int i;

	if (margin < 1)
		return;

	mask_buffer = MEM_callocN(sizeof(char) * num_pixels, "BakeMask");

	/* only extend to pixels outside the mask area */
	for (i=0; i < num_pixels; i++) {
		if (pixel_array[i].primitive_id != -1) {
			mask_buffer[i] = FILTER_MASK_USED;
		}
	}

	RE_bake_ibuf_filter(ibuf, mask_buffer, margin);

	MEM_freeN(mask_buffer);
}


/*** PSEUDO-CODE ***
 @brecht:
 if (active_to_selected and not normal baking):
 (this can be used to transfer the combined shader from a high poly object to a low poly)

 Go over pixel_array, and for every primitive_id, u, v, casts a ray to
 the other object which should return the primitive_id, u, v of the hit point.

 We then populate the pixel_array with this data, and all should work (we need to pass the high-poly object
 to the bake routine, naturally).

 I believe this 'ray' function is where cage, blockers, ... would be taken into consideration.
 Though to be honest cage/blockers/... may only be really needed for normal baking.

 Question: can I use snapObjectsRayEx? Or it will be too slow?

 elif (active_to_selected and normal baking) {
 ...? what do we do?

 one option is to bake the normal of the high poly object (in a similar fashion as described above),
 and calculate the real map "here". I'm not sure
 }
 */

/* Util macros */
#define OUT_OF_MEMORY() ((void)printf("Baking: Out of memory\n"))


typedef struct SpaceTransform {
	float local2target[4][4];
	float target2local[4][4];

} SpaceTransform;

/*
 * This function returns the coordinate and normal of a barycentric u,v for a face defined by the primitive_id index.
 */
static void get_point_from_barycentric(MFace *mface, MVert *mvert, int primitive_id, float u, float v, float cage_extrusion, float r_co[3], float r_dir[3])
{
	MFace *mf = &mface[primitive_id];
	MVert *v1 = &mvert[mf->v1];
	MVert *v2 = &mvert[mf->v2];
	MVert *v3 = &mvert[mf->v3];

	//TODO, math
	r_co[0] = 0.0f;
	r_co[1] = 0.0f;
	r_co[2] = 0.0f;

	r_dir[0] = 0.0f;
	r_dir[1] = 0.0f;
	r_dir[2] = 1.0f;
}

/*
 * This function returns the barycentric u,v of a face for a coordinate. The face is defined by its index.
 */
static void get_barycentric_from_point(MFace *mface, MVert  *mvert, int index, float co[3], int *primitive_id, float *u, float *v)
{
	primitive_id = index;

	MFace *mf = &mface[index];
	MVert *v1 = &mvert[mf->v1];
	MVert *v2 = &mvert[mf->v2];
	MVert *v3 = &mvert[mf->v3];

	// TODO, math
	*u = 0.0f;
	*v = 1.0f;
}

/*
 * This function populates pixel_array if returns TRUE
 */
static bool cast_ray_highpoly(BVHTreeFromMesh *treeData, BakePixel *pixel_array, float co[3], float dir[3])
{
	int primitive_id;
	float u;
	float v;

	BVHTreeRayHit hit;
	hit.index = -1;
	hit.dist = 10000.0f; /* TODO: we should use FLT_MAX here, but sweepsphere code isn't prepared for that */

	/* cast ray */
	BLI_bvhtree_ray_cast(treeData->tree, co, dir, 0.0f, &hit, treeData->raycast_callback, treeData);

	if (hit.index != -1) {
		/* cull backface */
		const float dot = dot_v3v3(dir, hit.no);
		if (dot >= 0.0f) {
			pixel_array->primitive_id = -1;
			return false;
		}

		get_barycentric_from_point(treeData->face, treeData->vert, hit.index, hit.co, &primitive_id, &u, &v);

		pixel_array->primitive_id = primitive_id;
		pixel_array->u = u;
		pixel_array->v = v;
		return true;
	}

	pixel_array->primitive_id = -1;
	return false;
}

void RE_populate_bake_pixels_from_object(Mesh *me_low, Mesh *me_high, BakePixel pixel_array[], const int num_pixels, const float cage_extrusion)
{
	int i;
	int primitive_id;
	float u, v;

	DerivedMesh *target = CDDM_from_mesh(me_high);

	BVHTreeFromMesh treeData = {NULL,};

	MFace *mface = CustomData_get_layer(&me_low->fdata, CD_MFACE);
	MVert *mvert = CustomData_get_layer(&me_low->vdata, CD_MVERT);

	/* Create a bvh-tree of the given target */
	bvhtree_from_mesh_faces(&treeData, target, 0.0, 2, 6);
	if (treeData.tree == NULL) {
		OUT_OF_MEMORY();
		return;
	}

	for (i=0; i < num_pixels; i++) {
		float co[3];
		float dir[3];

		primitive_id = pixel_array[i].primitive_id;

		if (primitive_id == -1)
			continue;

		u = pixel_array[i].u;
		v = pixel_array[i].v;

		/* calculate from low poly mesh cage */
		get_point_from_barycentric(mface, mvert, primitive_id, u, v, cage_extrusion, co, dir);

		/* cast ray */
		cast_ray_highpoly(&treeData, &pixel_array[i], co, dir);
	}

	free_bvhtree_from_mesh(&treeData);
	target->release(target);
}

void RE_populate_bake_pixels(Mesh *me, BakePixel pixel_array[], const int width, const int height)
{
	BakeData bd;
	const int num_pixels = width * height;
	int i, a;
	int p_id;
	MTFace *mtface;
	MFace *mface;

	/* we can't bake in edit mode */
	if (me->edit_btmesh)
		return;

	bd.pixel_array = pixel_array;
	bd.width = width;

	/* initialize all pixel arrays so we know which ones are 'blank' */
	for (i=0; i < num_pixels; i++) {
		pixel_array[i].primitive_id = -1;
	}

	zbuf_alloc_span(&bd.zspan, width, height, R.clipcrop);

	mtface = CustomData_get_layer(&me->fdata, CD_MTFACE);
	mface = CustomData_get_layer(&me->fdata, CD_MFACE);

	if (mtface == NULL)
		return;

	p_id = -1;
	for (i = 0; i < me->totface; i++) {
		float vec[4][2];
		MTFace *mtf = &mtface[i];
		MFace *mf = &mface[i];

		bd.primitive_id = ++p_id;

		for (a = 0; a < 4; a++) {
			/* Note, workaround for pixel aligned UVs which are common and can screw up our intersection tests
			 * where a pixel gets in between 2 faces or the middle of a quad,
			 * camera aligned quads also have this problem but they are less common.
			 * Add a small offset to the UVs, fixes bug #18685 - Campbell */
			vec[a][0] = mtf->uv[a][0] * (float)width - (0.5f + 0.001f);
			vec[a][1] = mtf->uv[a][1] * (float)height - (0.5f + 0.002f);
		}

		zspan_scanconvert(&bd.zspan, (void *)&bd, vec[0], vec[1], vec[2], store_bake_pixel);

		/* 4 vertices in the face */
		if (mf->v4 != 0) {
			bd.primitive_id = ++p_id;
			zspan_scanconvert(&bd.zspan, (void *)&bd, vec[0], vec[2], vec[3], store_bake_pixel);
		}
	}

	zbuf_free_span(&bd.zspan);
}


#if 0
static bool bake_uv(BakePixel UNUSED(pixel_array[]), int num_pixels, int depth, float result[])
{
	/* temporarily fill the result array with a normalized data */
	int i, j;
	for (i=0; i< num_pixels; i++) {
		int offset = i * depth;

		for (j=0; j< depth; j++) {
			result[offset + j] = (float) i / num_pixels;
		}
	}
	return true;
}
#else
/* not the real UV, but the internal per-face UV instead
   I'm using it to test if everything is correct */
static bool bake_uv(BakePixel pixel_array[], int num_pixels, int depth, float result[])
{
	int i;

	for (i=0; i < num_pixels; i++) {
		int offset = i * depth;
		result[offset] = pixel_array[i].u;
		result[offset + 1] = pixel_array[i].v;
	}

	return true;
}
#endif

bool RE_internal_bake(Render *UNUSED(re), Object *UNUSED(object), BakePixel pixel_array[], int num_pixels, int depth, ScenePassType pass_type, float result[])
{
	switch (pass_type) {
		case SCE_PASS_UV:
		{
			return bake_uv(pixel_array, num_pixels, depth, result);
			break;
		}
		default:
			break;
	}
	return false;
}

int RE_pass_depth(ScenePassType pass_type)
{
	/* IMB_buffer_byte_from_float assumes 4 channels
	   making it work for now - XXX */
	return 4;

	switch (pass_type) {
		case SCE_PASS_Z:
		case SCE_PASS_AO:
		case SCE_PASS_MIST:
		{
			return 1;
		}
		case SCE_PASS_UV:
		{
			return 2;
		}
		case SCE_PASS_RGBA:
		{
			return 4;
		}
		case SCE_PASS_COMBINED:
		case SCE_PASS_DIFFUSE:
		case SCE_PASS_SPEC:
		case SCE_PASS_SHADOW:
		case SCE_PASS_REFLECT:
		case SCE_PASS_NORMAL:
		case SCE_PASS_VECTOR:
		case SCE_PASS_REFRACT:
		case SCE_PASS_INDEXOB:// XXX double check
		case SCE_PASS_INDIRECT:
		case SCE_PASS_RAYHITS: // XXX double check
		case SCE_PASS_EMIT:
		case SCE_PASS_ENVIRONMENT:
		case SCE_PASS_INDEXMA:
		case SCE_PASS_DIFFUSE_DIRECT:
		case SCE_PASS_DIFFUSE_INDIRECT:
		case SCE_PASS_DIFFUSE_COLOR:
		case SCE_PASS_GLOSSY_DIRECT:
		case SCE_PASS_GLOSSY_INDIRECT:
		case SCE_PASS_GLOSSY_COLOR:
		case SCE_PASS_TRANSM_DIRECT:
		case SCE_PASS_TRANSM_INDIRECT:
		case SCE_PASS_TRANSM_COLOR:
		case SCE_PASS_SUBSURFACE_DIRECT:
		case SCE_PASS_SUBSURFACE_INDIRECT:
		case SCE_PASS_SUBSURFACE_COLOR:
		default:
		{
			return 3;
		}
	}
}
