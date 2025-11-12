#!/usr/bin/env python3
"""Extract static frames from Chebyshev animation GIFs for paper figures."""

from PIL import Image
import os

def extract_frame(gif_path, frame_number, output_path):
    """Extract a specific frame from a GIF animation."""
    with Image.open(gif_path) as img:
        img.seek(frame_number)
        img.save(output_path, 'PNG')
        print(f"Extracted frame {frame_number} from {gif_path} -> {output_path}")

def main():
    # Create output directory
    os.makedirs('paper/figures', exist_ok=True)

    # Extract frames for different N values at rotation angle ≈ 0° (frame 0)
    # and at rotation angle ≈ 60° (frame 50 out of 300 total)

    n_values = [3, 4, 5, 6, 12]

    for n in n_values:
        gif_path = f'chebyshev_gifs/chebyshev_animation_N{n}.gif'

        # Frame 0: rotation angle = 0°
        output_path_0 = f'paper/figures/chebyshev_N{n}_angle0.png'
        extract_frame(gif_path, 0, output_path_0)

        # Frame 50: rotation angle ≈ 60° (50/300 * 360° = 60°)
        if n == 5:  # Only for N=5, extract additional angle for comparison
            output_path_60 = f'paper/figures/chebyshev_N{n}_angle60.png'
            extract_frame(gif_path, 50, output_path_60)

    print("\nSuccessfully extracted all figures for the paper!")

if __name__ == "__main__":
    main()
