#pragma once

#include <glm.hpp>

#define GM_VSYNC_MODE DoubleBuffered

namespace Gogaman
{
	struct Config
	{
		static Config &GetConfig()
		{
			static Config instance;
			return instance;
		}

		//Window
			//Rendering resolution scale
			const float resScale        = 1.0f;
			//Window resolution
			const uint16_t screenWidth  = 3800;
			const uint16_t screenHeight = 2100;
			const float aspectRatio     = float(screenWidth) / float(screenHeight);

		//Controls
			const float mouseSensitivity    = 0.1f;
			const float cameraMovementSpeed = 3.0f;

		//Depth of field
			bool dof                = false;
			bool dofKeyPressed      = false;
			const float dofResScale = 1.0f;

		//Camera
			//Distance to the point of focus | Unit: meters
			const float focalDistance = 10.0f;
			//Ratio of the aperture | Unit: f-stops
			const float fStop = 0.01f;
			//Distance from lens to film | Unit: millimeters
			const float focalLength = 50.0f;
	};
}

#define GM_CONFIG Gogaman::Config::GetConfig()