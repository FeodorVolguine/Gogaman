#pragma once

#ifdef GM_PLATFORM_WINDOWS
	#include "Platform/Vulkan/RenderHardwareInterface/VulkanRenderCommandRecorder.h"
#else
	#error "Unsupported platform"
#endif