#!/usr/bin/env python3
"""
Extract frames from rendered Chebyshev videos.

This unified tool replaces the legacy extraction scripts (extract_paper_figures.py,
extract_paper_figures_vector.py, extract_single_frame.py) by extracting frames
directly from the rendered video files using ffmpeg.

Usage:
    # Extract single frame
    python extract_frames_from_videos.py --video chebyshev_videos/chebyshev_N3.mp4 --time 0.0 --output paper_figures/figure_N3.png

    # Batch extract paper figures (N=3,5,10 at φ=0)
    python extract_frames_from_videos.py --batch-paper-figures

    # Extract frame at specific angle φ
    python extract_frames_from_videos.py --video chebyshev_videos/chebyshev_N5.mp4 --phi 1.57 --output test_frame.png

Features:
- Extracts high-quality PNG frames from rendered videos
- No re-rendering needed - uses existing video files
- Preserves portrait orientation (1080x1920)
- Optional PDF conversion for LaTeX inclusion
- Batch mode for generating all paper figures at once
"""

import argparse
import subprocess
import sys
from pathlib import Path


def extract_frame(video_path: str, timestamp: float, output_path: str) -> bool:
    """
    Extract a single frame from video at specified timestamp using ffmpeg.

    Args:
        video_path: Path to input video file
        timestamp: Time in seconds (e.g., 0.0 for φ=0)
        output_path: Path for output PNG file

    Returns:
        True if successful, False otherwise
    """
    video_file = Path(video_path)
    output_file = Path(output_path)

    if not video_file.exists():
        print(f"Error: Video file not found: {video_path}", file=sys.stderr)
        return False

    # Create output directory if needed
    output_file.parent.mkdir(parents=True, exist_ok=True)

    # ffmpeg command to extract frame at timestamp
    # -ss: seek to timestamp
    # -i: input video
    # -vframes 1: extract exactly 1 frame
    # -q:v 1: highest quality (1 is best for PNG)
    cmd = [
        'ffmpeg',
        '-y',  # Overwrite output file if exists
        '-ss', str(timestamp),
        '-i', str(video_file),
        '-vframes', '1',
        '-q:v', '1',  # Highest quality
        str(output_file)
    ]

    print(f"Extracting frame from {video_file.name} at t={timestamp}s -> {output_file.name}")

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            check=True
        )
        print(f"✓ Successfully extracted frame to {output_file}")
        return True
    except subprocess.CalledProcessError as e:
        print(f"Error: ffmpeg failed: {e.stderr}", file=sys.stderr)
        return False
    except FileNotFoundError:
        print("Error: ffmpeg not found. Please install ffmpeg.", file=sys.stderr)
        return False


def convert_to_pdf(png_path: str, pdf_path: str = None) -> bool:
    """
    Convert PNG to PDF using ImageMagick (optional step for LaTeX).

    Args:
        png_path: Path to input PNG file
        pdf_path: Path for output PDF (optional, defaults to .pdf extension)

    Returns:
        True if successful, False otherwise
    """
    png_file = Path(png_path)

    if not png_file.exists():
        print(f"Error: PNG file not found: {png_path}", file=sys.stderr)
        return False

    if pdf_path is None:
        pdf_file = png_file.with_suffix('.pdf')
    else:
        pdf_file = Path(pdf_path)

    cmd = ['convert', str(png_file), str(pdf_file)]

    print(f"Converting {png_file.name} to PDF...")

    try:
        subprocess.run(cmd, capture_output=True, text=True, check=True)
        print(f"✓ Successfully converted to {pdf_file}")
        return True
    except subprocess.CalledProcessError as e:
        print(f"Error: ImageMagick convert failed: {e.stderr}", file=sys.stderr)
        return False
    except FileNotFoundError:
        print("Error: ImageMagick 'convert' not found. Skipping PDF conversion.", file=sys.stderr)
        return False


def phi_to_timestamp(phi_radians: float, N: int) -> float:
    """
    Convert rotation angle φ (radians) to video timestamp (seconds).

    Videos rotate full 2π in N×10 seconds, so:
    timestamp = φ / (2π) × (N × 10)

    Args:
        phi_radians: Rotation angle in radians (0 to 2π)
        N: Number of roots

    Returns:
        Timestamp in seconds
    """
    import math
    duration = N * 10.0  # Total video duration
    timestamp = (phi_radians / (2 * math.pi)) * duration
    return timestamp


def batch_extract_paper_figures():
    """
    Batch mode: Extract all paper figures (N=3,5,10 at φ=0).

    Generates:
    - paper_figures/paper_figure_N3_phi0.png
    - paper_figures/paper_figure_N5_phi0.png
    - paper_figures/paper_figure_N10_phi0.png

    And optionally converts to PDF for LaTeX.
    """
    paper_configs = [
        {'N': 3, 'video': 'media/videos/chebyshev_manim/Chebyshev_N3/Chebyshev_N3.mp4', 'phi': 0.0},
        {'N': 5, 'video': 'media/videos/chebyshev_manim/Chebyshev_N5/Chebyshev_N5.mp4', 'phi': 0.0},
        {'N': 10, 'video': 'media/videos/chebyshev_manim/Chebyshev_N10/Chebyshev_N10.mp4', 'phi': 0.0},
    ]

    print("\n=== Batch Extracting Paper Figures ===\n")

    success_count = 0
    for config in paper_configs:
        N = config['N']
        video = config['video']
        phi = config['phi']
        timestamp = phi_to_timestamp(phi, N)

        # Output paths
        output_png = f"paper_figures/paper_figure_N{N}_phi0.png"
        output_pdf = f"paper_figures/paper_figure_N{N}_phi0.pdf"

        # Extract frame
        if extract_frame(video, timestamp, output_png):
            success_count += 1
            # Optional: Convert to PDF
            convert_to_pdf(output_png, output_pdf)

        print()  # Blank line between operations

    print(f"\n=== Complete: {success_count}/{len(paper_configs)} frames extracted ===\n")


def main():
    parser = argparse.ArgumentParser(
        description='Extract frames from Chebyshev Circle videos',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )

    # Mode selection
    parser.add_argument(
        '--batch-paper-figures',
        action='store_true',
        help='Batch extract all paper figures (N=3,5,10 at φ=0)'
    )

    # Single frame extraction
    parser.add_argument(
        '--video',
        type=str,
        help='Path to input video file'
    )

    parser.add_argument(
        '--time',
        type=float,
        help='Timestamp in seconds to extract frame'
    )

    parser.add_argument(
        '--phi',
        type=float,
        help='Alternative to --time: specify rotation angle φ in radians'
    )

    parser.add_argument(
        '--output',
        type=str,
        help='Path for output PNG file'
    )

    parser.add_argument(
        '--pdf',
        action='store_true',
        help='Also convert to PDF (requires ImageMagick)'
    )

    args = parser.parse_args()

    # Batch mode
    if args.batch_paper_figures:
        batch_extract_paper_figures()
        return

    # Single frame mode
    if not args.video or not args.output:
        parser.error("For single frame extraction, --video and --output are required")

    # Determine timestamp
    if args.phi is not None:
        # Extract N from video filename (e.g., chebyshev_N3.mp4 -> N=3)
        import re
        match = re.search(r'N(\d+)', args.video)
        if not match:
            print("Error: Could not determine N from video filename", file=sys.stderr)
            sys.exit(1)
        N = int(match.group(1))
        timestamp = phi_to_timestamp(args.phi, N)
        print(f"φ = {args.phi:.3f} rad -> t = {timestamp:.3f}s (N={N})")
    elif args.time is not None:
        timestamp = args.time
    else:
        parser.error("Either --time or --phi must be specified")

    # Extract frame
    if extract_frame(args.video, timestamp, args.output):
        # Optional PDF conversion
        if args.pdf:
            convert_to_pdf(args.output)
    else:
        sys.exit(1)


if __name__ == '__main__':
    main()
