#include "pch.h"
#include "OpenGL_Texture1D.h"

#include "Gogaman/Core/Base.h"
#include "Gogaman/Core/Logging/Log.h"

#include <glad.h>

namespace Gogaman
{
	Texture1D::Texture1D()
	{
		glCreateTextures(GL_TEXTURE_1D, 1, &m_RendererID);
		GM_LOG_CORE_TRACE("Created texture with ID: %d", m_RendererID);
	}

	Texture1D::~Texture1D()
	{}

	void Texture1D::Generate(const uint16_t width, const uint8_t *imageData)
	{
		GM_ASSERT(width > 0, "Failed to generate texture1D: invalid width")
		GM_ASSERT((interpolation != TextureInterpolation::Trilinear) || levels != 1, "Failed to generate texture1D with trilinear interpolation: texture has only 1 level")
		
		this->width = width;

		if(levels == 0)
			levels = (int)floor(log2(width)) + 1;

		glTextureStorage1D(m_RendererID, static_cast<GLsizei>(levels), GetNativeTextureInternalFormat(internalFormat), width);
		if(imageData != nullptr)
			glTextureSubImage1D(m_RendererID, 0, 0, width, GetNativeTextureFormat(format), GL_UNSIGNED_BYTE, imageData);

		//Set properties
		glTextureParameteri(m_RendererID, GL_TEXTURE_WRAP_S,     GetNativeTextureWrap(wrapS));
		glTextureParameteri(m_RendererID, GL_TEXTURE_MIN_FILTER, GetNativeTextureInterpolationMin(interpolation));
		glTextureParameteri(m_RendererID, GL_TEXTURE_MAG_FILTER, GetNativeTextureInterpolationMag(interpolation));
		if(interpolation == TextureInterpolation::Anisotropic)
		{
			glTextureParameterf(m_RendererID, GL_TEXTURE_MAX_ANISOTROPY_EXT, GetMaxAnisotropicInterpolationSamples());
		}
		
		//Generate mipmap
		if(levels != 1)
			glGenerateTextureMipmap(m_RendererID);
	}
}