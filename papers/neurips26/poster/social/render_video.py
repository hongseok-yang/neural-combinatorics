"""Render the training animation (MP4 + GIF) from graphon snapshots.

Each input .npz holds one training run:
    steps   [n]        training step of each snapshot
    frames  [n, G, G]  the graphon on a G x G grid, uint8 (0..255 for W in [0, 1])
    exact   [n]        t(H, W) of the discretised graphon at each snapshot
    epochs             total number of training steps

    python render_video.py --runs k3.npz c5.npz h6.npz --out training
    python render_video.py --demo --out demo          # synthetic frames, layout check only

MP4 encoding needs ffmpeg; pass --ffmpeg PATH, or have imageio-ffmpeg importable.
"""

import argparse
import os
import subprocess

import numpy as np
from matplotlib import colormaps
from PIL import Image, ImageDraw, ImageFont

W, H = 1280, 720
MAIN = (0, 65, 145)            # KAIST Dark Blue
LIGHT = (95, 190, 235)         # KAIST Light Blue
WHITE = (255, 255, 255)
SOFT = (204, 217, 233)
FONT_DIR = r"C:\texlive\2025\texmf-dist\fonts\opentype\public\fira"
VIRIDIS = (colormaps["viridis"](np.linspace(0, 1, 256))[:, :3] * 255).astype(np.uint8)

PANEL = 320
PANEL_X = (64, 480, 896)
PANEL_Y = 204

# Per-pattern text.  `ref` lines are reference values from the paper's tables.
TEXT = {
    "k3": dict(tag="KNOWN OPTIMUM", title="Fewest triangles at edge density 2/3",
               name="triangle density", ref="optimum 0.2222"),
    "c5": dict(tag="OPEN PROBLEM", title="Fewest 5-cycles at edge density 4/7",
               name="5-cycle density", ref="conjectured optimum 0.0459"),
    "h6": dict(tag="NEW STRUCTURE", title="Fewest copies of H\u2086 at edge density 2/3",
               name="H\u2086 density", ref="k-partite 0.0329, constant 0.0260"),
}


def font(weight, size):
    return ImageFont.truetype(os.path.join(FONT_DIR, f"FiraSans-{weight}.otf"), size)


def heat(frame):
    """uint8 grid -> RGB image, origin at the bottom left as in the paper's figures."""
    rgb = VIRIDIS[frame[::-1]]
    return Image.fromarray(rgb).resize((PANEL, PANEL), Image.LANCZOS)


def demo_runs(n=120, g=96):
    """Synthetic stand-ins (noise fading into block patterns); for layout checks only."""
    rng = np.random.default_rng(0)
    x = (np.arange(g) + 0.5) / g
    xx, yy = np.meshgrid(x, x, indexing="ij")
    targets = {
        "k3": (np.floor(xx * 3) != np.floor(yy * 3)).astype(float),
        "c5": ((np.floor(xx * 2) != np.floor(yy * 2)) | (np.abs(xx - yy) > 0.3)).astype(float),
        "h6": (np.abs(((xx - yy + 0.5) % 1.0) - 0.5) > 0.12).astype(float),
    }
    runs = []
    for motif, target in targets.items():
        noise = rng.random((g, g)); noise = (noise + noise.T) / 2
        a = (np.arange(n) / (n - 1))[:, None, None] ** 0.5
        frames = ((1 - a) * (0.4 + 0.3 * noise) + a * target) * 255
        runs.append(dict(motif=motif, steps=np.arange(n) * 50, epochs=(n - 1) * 50,
                         frames=frames.astype(np.uint8), exact=np.linspace(0.3, 0.2, n)))
    return runs


def load(path):
    d = np.load(path)
    return dict(motif=str(d["motif"]), steps=d["steps"], epochs=int(d["epochs"]),
                frames=d["frames"], exact=d["exact"])


def base_canvas(runs):
    im = Image.new("RGB", (W, H), MAIN)
    d = ImageDraw.Draw(im)
    d.text((64, 40), "Gradient descent finds extremal graphs", font=font("Bold", 46), fill=WHITE)
    d.text((64, 102), "A neural network learns each graphon from a random initialisation",
           font=font("Regular", 23), fill=LIGHT)
    for run, x in zip(runs, PANEL_X):
        t = TEXT[run["motif"]]
        d.text((x, PANEL_Y - 34), t["tag"], font=font("Bold", 18), fill=LIGHT)
        d.rectangle((x - 2, PANEL_Y - 2, x + PANEL + 1, PANEL_Y + PANEL + 1), outline=WHITE, width=2)
        d.text((x, PANEL_Y + PANEL + 16), t["title"], font=font("Bold", 19), fill=WHITE)
        d.text((x, PANEL_Y + PANEL + 72), t["ref"], font=font("Regular", 18), fill=SOFT)
    d.text((64, H - 38), "Implicit Neural Representations for Variational Problems on Graphons"
           "  \u00b7  NeurIPS 2026", font=font("Regular", 16), fill=SOFT)
    return im


def render(runs, n_frames, hold_start, hold_end):
    base = base_canvas(runs)
    f_val, f_small = font("Medium", 18), font("Regular", 16)
    out = []
    for j in range(n_frames):
        u = (j / (n_frames - 1)) ** 2                     # more frames early, where most happens
        im = base.copy()
        d = ImageDraw.Draw(im)
        for run, x in zip(runs, PANEL_X):
            k = int(np.searchsorted(run["steps"], u * run["epochs"], side="right")) - 1
            k = max(0, min(k, len(run["steps"]) - 1))
            im.paste(heat(run["frames"][k]), (x, PANEL_Y))
            d.text((x, PANEL_Y + PANEL + 46), f"{TEXT[run['motif']]['name']} {run['exact'][k]:.4f}",
                   font=f_val, fill=WHITE)
        # training progress
        y = H - 62
        d.rectangle((64, y, W - 64, y + 5), fill=(51, 103, 167))
        d.rectangle((64, y, 64 + int((W - 128) * u), y + 5), fill=WHITE)
        d.text((W - 64, H - 38), f"training {100 * u:3.0f}%", font=f_small, fill=SOFT, anchor="ra")
        out.append(im)
    return [out[0]] * hold_start + out + [out[-1]] * hold_end


def find_ffmpeg(explicit):
    if explicit:
        return explicit
    try:
        import imageio_ffmpeg
        return imageio_ffmpeg.get_ffmpeg_exe()
    except ImportError:
        return None


def write_mp4(frames, path, fps, ffmpeg):
    cmd = [ffmpeg, "-y", "-loglevel", "error", "-f", "rawvideo", "-pix_fmt", "rgb24",
           "-s", f"{W}x{H}", "-r", str(fps), "-i", "-", "-c:v", "libx264", "-crf", "17",
           "-preset", "slow", "-pix_fmt", "yuv420p", "-movflags", "+faststart", path]
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE)
    for im in frames:
        proc.stdin.write(im.tobytes())
    proc.stdin.close()
    if proc.wait() != 0:
        raise RuntimeError("ffmpeg failed")


def write_gif(frames, path, fps, size=(800, 450), every=2):
    small = [im.resize(size, Image.LANCZOS) for im in frames[::every]]
    palette = small[-1].quantize(colors=255, method=Image.Quantize.MEDIANCUT)
    pal = [f.quantize(palette=palette, dither=Image.Dither.NONE) for f in small]
    pal[0].save(path, save_all=True, append_images=pal[1:], duration=int(1000 * every / fps),
                loop=0, optimize=False)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--runs", nargs=3, metavar="NPZ")
    ap.add_argument("--demo", action="store_true")
    ap.add_argument("--out", default="training", help="output path without extension")
    ap.add_argument("--fps", type=int, default=30)
    ap.add_argument("--seconds", type=float, default=11.0)
    ap.add_argument("--ffmpeg", default="")
    ap.add_argument("--still", action="store_true", help="also save first/middle/last frames")
    args = ap.parse_args()

    runs = demo_runs() if args.demo else [load(p) for p in args.runs]
    frames = render(runs, int(args.fps * args.seconds), hold_start=args.fps // 2,
                    hold_end=int(args.fps * 2.5))
    print(f"{len(frames)} frames, {len(frames) / args.fps:.1f} s")
    if args.still:
        n = len(frames)
        for tag, k in (("first", 0), ("mid", n // 3), ("last", n - 1)):
            frames[k].save(f"{args.out}_{tag}.png")
    ffmpeg = find_ffmpeg(args.ffmpeg)
    if ffmpeg:
        write_mp4(frames, args.out + ".mp4", args.fps, ffmpeg)
        print("wrote", args.out + ".mp4", os.path.getsize(args.out + ".mp4") // 1024, "KiB")
    else:
        print("no ffmpeg found: skipping the MP4")
    write_gif(frames, args.out + ".gif", args.fps)
    print("wrote", args.out + ".gif", os.path.getsize(args.out + ".gif") // 1024, "KiB")


if __name__ == "__main__":
    main()
