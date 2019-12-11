#include "pch.h"
#include "AbstractTexture.h"

#include "Texture.h"

#include "Device.h"

namespace Gogaman
{
	namespace RHI
	{
		AbstractTexture<Texture>::AbstractTexture(const Format format, const uint16_t width, const uint16_t height, const uint16_t depth, const uint8_t levelCount)
			: m_Width(width), m_Height(height), m_Depth(depth), m_LevelCount(levelCount), m_Format(format)
		{
			#if GM_RHI_DEBUGGING_ENABLED
				GM_DEBUG_ASSERT(m_Width  > 0, "Failed to construct texture | Width is 0");
				GM_DEBUG_ASSERT(m_Height > 0, "Failed to construct texture | Height is 0");
				GM_DEBUG_ASSERT(m_Depth  > 0, "Failed to construct texture | Depth is 0");

				GM_DEBUG_ASSERT(m_Width  <= g_Device->GetTextureWidthLimit(),  "Failed to construct texture | Width exceeds device limit");
				GM_DEBUG_ASSERT(m_Height <= g_Device->GetTextureHeightLimit(), "Failed to construct texture | Height exceeds device limit");
				GM_DEBUG_ASSERT(m_Depth  <= g_Device->GetTextureDepthLimit(),  "Failed to construct texture | Depth exceeds device limit");
			#endif
		}
	}
}