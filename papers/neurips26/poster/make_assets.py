"""Prepare the poster's image assets from the paper's figures.

The paper's heatmaps carry matplotlib axes; on the poster they are shown as bare
squares, so each one is cropped to its plot area.  Nothing is recomputed: every
pixel comes from ../figures or ../new_figures.

    python make_assets.py
"""

import os

import numpy as np
from PIL import Image

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.dirname(HERE)
OUT = os.path.join(HERE, "img")

# output name -> source figure (relative to the paper directory)
HEATMAPS = {
    # K3 density minimisation (Fig. 1)
    "k3_50": "new_figures/k3_50.png", "k3_67": "new_figures/k3_67.png",
    "k3_80": "new_figures/k3_80.png", "k3_57": "new_figures/k3_57.png",
    "k3_62": "new_figures/k3_62.png", "k3_71": "new_figures/k3_71.png",
    # larger cliques (Fig. 2)
    "k4_75": "new_figures/k4_75.png", "k5_80": "new_figures/k5_80.png",
    "k6_83": "new_figures/k6_83.png",
    # odd cycles (Figs. 3, 4)
    "c5_57": "new_figures/c5_57.png", "c5_62": "new_figures/c5_62.png",
    "c5_71": "new_figures/c5_71.png", "c5_67": "new_figures/c5_67.png",
    "c5_80": "new_figures/c5_80.png",
    "c7_57": "new_figures/c7_57.png", "c7_62": "new_figures/c7_62.png",
    "c7_71": "new_figures/c7_71.png", "c7_67": "new_figures/c7_67.png",
    "c7_80": "new_figures/c7_80.png",
    # H6 (Fig. 5)
    "h6_67": "new_figures/222_67.png", "h6_75": "new_figures/222_75.png",
    "h6_80": "new_figures/222_80.png",
    # large deviations (Fig. 6 and appendix)
    "ld_k3": "new_figures/upperdeviation_k3_10_50.png",
    "ld_c4": "new_figures/upperdeviation_c4_10_50.png",
    "ld_c5": "new_figures/upperdeviation_c5_10_50.png",
    "ld_k13": "new_figures/upperdeviation_k13_10_50.png",
    "ld_lower": "new_figures/lowerdeviation_k3_80_5.png",
    # ablation and baselines (appendix)
    "abl_ours": "figures/baseline.png", "abl_reg": "figures/noconstraint.png",
    "abl_sbm": "new_figures/sbm_train_4.png", "abl_tree": "new_figures/tree_train_1.png",
    "abl_lr_low": "figures/noscaling-lowlr.png", "abl_lr_high": "figures/noscaling-highlr.png",
    # Petersen graph (appendix)
    "pet_67": "new_figures/pet_67.png", "pet_71": "new_figures/pet_71.png",
}

# already bare squares: copied as they are
PLAIN = {f"layer_{i}": f"new_figures/layer_{i}.png" for i in range(1, 7)}


def flatten(path):
    im = Image.open(path).convert("RGBA")
    bg = Image.new("RGBA", im.size, "white")
    bg.alpha_composite(im)
    return bg.convert("RGB")


def plot_area(im):
    """Bounding box of the heatmap: the viridis pixels are the only saturated ones
    (axes, ticks and labels are grey)."""
    a = np.asarray(im).astype(int)
    colored = (a.max(axis=2) - a.min(axis=2)) > 40
    rows = np.where(colored.mean(axis=1) > 0.5)[0]
    cols = np.where(colored.mean(axis=0) > 0.5)[0]
    return cols[0], rows[0], cols[-1] + 1, rows[-1] + 1


def main():
    os.makedirs(OUT, exist_ok=True)
    for name, rel in HEATMAPS.items():
        im = flatten(os.path.join(SRC, rel))
        x0, y0, x1, y1 = plot_area(im)
        crop = im.crop((x0 + 1, y0 + 1, x1 - 1, y1 - 1))   # drop the axes spine
        side = min(crop.size)
        crop = crop.crop((0, 0, side, side))
        crop.save(os.path.join(OUT, name + ".png"))
        print(f"{name:10s} {rel:45s} -> {crop.size}")
    for name, rel in PLAIN.items():
        im = flatten(os.path.join(SRC, rel))
        im.save(os.path.join(OUT, name + ".png"))
        print(f"{name:10s} {rel:45s} -> {im.size}")

    # Viridis colour bar, drawn from matplotlib's own colormap.
    from matplotlib import colormaps
    ramp = (colormaps["viridis"](np.linspace(0, 1, 1024))[:, :3] * 255).astype(np.uint8)
    bar = np.repeat(ramp[None, :, :], 48, axis=0)
    Image.fromarray(bar).save(os.path.join(OUT, "colorbar.png"))
    print("colorbar")


if __name__ == "__main__":
    main()
