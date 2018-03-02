extern crate image;

use image::*;


enum DitherMode {
    Plain,
    ErrorDiffusion
}

fn find_closest_colors(color: &Rgb<u8>, colors: &[Rgb<u8>]) -> Rgb<u8> {
    let best = colors.iter().max_by(|&a, &b| {
        pixel_similarity(a, color).partial_cmp(&pixel_similarity(b, color)).unwrap()
    }).unwrap();
    best.clone()
}

fn from_multiple_rgb_hex(colors: &[&str]) -> Vec<Rgb<u8>> {
    colors.iter().map(|&x| rgb(x)).collect::<Vec<_>>()
}

fn rgb(hex: &str) -> Rgb<u8> {
    let (rrng, grng, brng) = if hex.len() == 3 {
        (0..1, 1..2, 2..3)
    } else {
        (0..2, 2..4, 4..6)
    };
    let r = u8::from_str_radix(&hex[rrng], 16).unwrap();
    let g = u8::from_str_radix(&hex[grng], 16).unwrap();
    let b = u8::from_str_radix(&hex[brng], 16).unwrap();

    Rgb { data: [r, g, b] }
}

fn pixel_similarity(p1: &Rgb<u8>, p2: &Rgb<u8>) -> f32 {
    let norm1: f32 = p1.data.iter().map(|&x| (x as f32).powi(2)).sum();
    let norm2: f32 = p2.data.iter().map(|&x| (x as f32).powi(2)).sum();
    let dot: f32 = p1.data.iter().zip(p2.data.iter()).map(|(&x, &y)| (x as f32 * y as f32)).sum();
    if norm1 == 0f32 || norm2 == 0f32 {
        0f32
    } else {
        1f32 - dot / (norm1 * norm2)
    }
}

fn dither_plain(img: &ImageBuffer<>, palette: &[Rgb<u8>]) -> Option<ImageBuffer> {

}

fn main() {
}
