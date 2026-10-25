from pathlib import Path
from PIL import Image, ImageDraw, ImageFilter
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
ASSETS = ROOT / "assets"
ASSETS.mkdir(exist_ok=True)
S = 1024
img = Image.new("RGBA", (S, S), (0, 0, 0, 0))

# Deep navy to teal diagonal gradient.
yy, xx = np.mgrid[0:S, 0:S].astype(np.float32)
t = np.clip((xx * 0.52 + yy * 0.48) / (S - 1), 0, 1)
c1 = np.array([8, 20, 34], dtype=np.float32)
c2 = np.array([8, 153, 155], dtype=np.float32)
grad = c1[None, None, :] * (1 - t[..., None]) + c2[None, None, :] * t[..., None]
radial = np.clip(1.0 - np.sqrt((xx - 770) ** 2 + (yy - 770) ** 2) / 760.0, 0, 1)
grad += np.array([0, 92, 85], dtype=np.float32)[None, None, :] * (radial[..., None] ** 2) * 0.55
base = Image.fromarray(np.clip(grad, 0, 255).astype(np.uint8), "RGB").convert("RGBA")

margin = 34
radius = 220
mask = Image.new("L", (S, S), 0)
ImageDraw.Draw(mask).rounded_rectangle(
    (margin, margin, S - margin, S - margin), radius=radius, fill=255
)
img.paste(base, (0, 0), mask)

# Top glass highlight.
highlight = Image.new("RGBA", (S, S), (0, 0, 0, 0))
ImageDraw.Draw(highlight).rounded_rectangle(
    (margin + 4, margin + 4, S - margin - 4, S // 2),
    radius=radius - 4, fill=(255, 255, 255, 22)
)
highlight = highlight.filter(ImageFilter.GaussianBlur(26))
img.alpha_composite(highlight)

# Border rings.
border = Image.new("RGBA", (S, S), (0, 0, 0, 0))
bd = ImageDraw.Draw(border)
bd.rounded_rectangle(
    (margin, margin, S - margin, S - margin), radius=radius,
    outline=(210, 255, 252, 70), width=10
)
bd.rounded_rectangle(
    (margin + 20, margin + 20, S - margin - 20, S - margin - 20),
    radius=radius - 20, outline=(255, 255, 255, 22), width=3
)
img.alpha_composite(border)

# Play-button shadow.
shadow = Image.new("RGBA", (S, S), (0, 0, 0, 0))
ImageDraw.Draw(shadow).ellipse((252, 206, 772, 726), fill=(0, 12, 18, 145))
img.alpha_composite(shadow.filter(ImageFilter.GaussianBlur(38)))

# Light play disc.
disc_box = (250, 190, 750, 690)
disc = Image.new("RGBA", (S, S), (0, 0, 0, 0))
dd = ImageDraw.Draw(disc)
dd.ellipse(disc_box, fill=(244, 255, 253, 255))
shade = Image.new("RGBA", (S, S), (0, 0, 0, 0))
ImageDraw.Draw(shade).ellipse((250, 390, 750, 710), fill=(126, 237, 229, 60))
shade = shade.filter(ImageFilter.GaussianBlur(72))
disc.alpha_composite(shade)
dd.ellipse(disc_box, outline=(255, 255, 255, 255), width=12)
dd.ellipse((270, 210, 730, 670), outline=(8, 112, 118, 45), width=4)
img.alpha_composite(disc)

# Teal play triangle.
tri = Image.new("RGBA", (S, S), (0, 0, 0, 0))
ImageDraw.Draw(tri).polygon(
    [(440, 330), (440, 560), (620, 445)], fill=(8, 151, 153, 255)
)
img.alpha_composite(tri.filter(ImageFilter.GaussianBlur(1.2)))
gloss = Image.new("RGBA", (S, S), (0, 0, 0, 0))
ImageDraw.Draw(gloss).polygon(
    [(444, 342), (444, 438), (575, 409)], fill=(255, 255, 255, 60)
)
img.alpha_composite(gloss.filter(ImageFilter.GaussianBlur(8)))

# Download badge shadow.
badge_shadow = Image.new("RGBA", (S, S), (0, 0, 0, 0))
ImageDraw.Draw(badge_shadow).ellipse((588, 600, 928, 940), fill=(0, 10, 18, 160))
img.alpha_composite(badge_shadow.filter(ImageFilter.GaussianBlur(28)))

# Coral download badge.
badge = Image.new("RGBA", (S, S), (0, 0, 0, 0))
bdd = ImageDraw.Draw(badge)
bdd.ellipse((610, 610, 910, 910), fill=(255, 76, 103, 255),
            outline=(255, 220, 226, 250), width=13)
bdd.ellipse((630, 630, 890, 890), fill=(255, 91, 116, 255))
sheen = Image.new("RGBA", (S, S), (0, 0, 0, 0))
ImageDraw.Draw(sheen).ellipse((642, 638, 878, 780), fill=(255, 226, 229, 105))
sheen = sheen.filter(ImageFilter.GaussianBlur(34))
badge.alpha_composite(sheen)
depth = Image.new("RGBA", (S, S), (0, 0, 0, 0))
ImageDraw.Draw(depth).ellipse((650, 790, 870, 900), fill=(155, 19, 49, 52))
depth = depth.filter(ImageFilter.GaussianBlur(32))
badge.alpha_composite(depth)
img.alpha_composite(badge)

# White download arrow and tray.
arrow = Image.new("RGBA", (S, S), (0, 0, 0, 0))
ad = ImageDraw.Draw(arrow)
ad.rounded_rectangle((737, 669, 783, 807), radius=22, fill=(255, 255, 255, 255))
ad.polygon([(687, 785), (833, 785), (760, 862)], fill=(255, 255, 255, 255))
ad.rounded_rectangle((684, 854, 836, 878), radius=12, fill=(255, 255, 255, 255))
ad.rounded_rectangle((699, 842, 714, 870), radius=6, fill=(255, 255, 255, 255))
ad.rounded_rectangle((806, 842, 821, 870), radius=6, fill=(255, 255, 255, 255))
img.alpha_composite(arrow.filter(ImageFilter.GaussianBlur(0.6)))

# Keep all glow precisely inside the rounded tile.
final_alpha = Image.composite(img.getchannel("A"), Image.new("L", (S, S), 0), mask)
img.putalpha(final_alpha)

png_path = ASSETS / "douyin_daily_icon.png"
ico_path = ASSETS / "douyin_daily_icon.ico"
img.save(png_path, "PNG")
sizes = [(16, 16), (20, 20), (24, 24), (32, 32), (40, 40), (48, 48), (64, 64), (128, 128), (256, 256)]
img.save(ico_path, format="ICO", sizes=sizes)

preview = Image.new("RGBA", (720, 320), (238, 242, 246, 255))
preview.alpha_composite(img.resize((256, 256), Image.Resampling.LANCZOS), (32, 32))
for i, sz in enumerate((16, 20, 24, 32, 40, 48, 64, 128)):
    thumb = img.resize((sz, sz), Image.Resampling.LANCZOS)
    preview.alpha_composite(thumb, (320 + (i % 4) * 90, 45 + (i // 4) * 120))
preview.save(ASSETS / "icon_preview.png")
print(png_path)
print(ico_path, ico_path.stat().st_size)

# Desktop shortcuts cannot reliably resolve an icon under a non-ASCII path,
# so deploy the ICO to an ASCII-only LocalAppData directory as well.
import os
import shutil
deploy_dir = Path(os.environ["LOCALAPPDATA"]) / "DouyinDailyExtractor"
deploy_dir.mkdir(parents=True, exist_ok=True)
deployed_ico = deploy_dir / "douyin_daily_icon.ico"
shutil.copy2(ico_path, deployed_ico)
print(deployed_ico)
