
import common._
import scala.collection._

package object scalashop {

  /** The value of every pixel is represented as a 32 bit integer. */
  type RGBA = Int

  /** Returns the red component. */
  def red(c: RGBA): Int = (0xff000000 & c) >>> 24

  /** Returns the green component. */
  def green(c: RGBA): Int = (0x00ff0000 & c) >>> 16

  /** Returns the blue component. */
  def blue(c: RGBA): Int = (0x0000ff00 & c) >>> 8

  /** Returns the alpha component. */
  def alpha(c: RGBA): Int = (0x000000ff & c) >>> 0

  /** Used to create an RGBA value from separate components. */
  def rgba(r: Int, g: Int, b: Int, a: Int): RGBA = {
    (r << 24) | (g << 16) | (b << 8) | (a << 0)
  }

  def avg_rgba(rgba_list: List[RGBA]): RGBA = {
    val n = rgba_list.length
    val r = rgba_list.map(red(_)).sum / n
    val g = rgba_list.map(green(_)).sum / n
    val b = rgba_list.map(blue(_)).sum / n
    val a = rgba_list.map(alpha(_)).sum / n
    // println(s"$rgba_list - len: ${rgba_list.length} - ${rgba(r,g,b,a)}")
    rgba(r, g, b, a)
  }

  /** Restricts the integer into the specified range. */
  def clamp(v: Int, min: Int, max: Int): Int = {
    if (v < min) min
    else if (v > max) max
    else v
  }

  def valid(v: Int, min: Int, max: Int): Boolean = {
    v >= min && v <= max
  }

  /** Image is a two-dimensional matrix of pixel values. */
  class Img(val width: Int, val height: Int, private val data: Array[RGBA]) {
    def this(w: Int, h: Int) = this(w, h, new Array(w * h))
    def apply(x: Int, y: Int): RGBA = data(y * width + x)
    def update(x: Int, y: Int, c: RGBA): Unit = data(y * width + x) = c
    def apply_clamped(x: Int, y: Int): RGBA = {
      apply(clamp(x, 0, width  - 1),
            clamp(y, 0, height - 1))
    }
    def valid_x(x: Int) = valid(x, 0, width - 1)
    def valid_y(y: Int) = valid(y, 0, height - 1)
  }

  /** Computes the blurred RGBA value of a single pixel of the input image. */
  def boxBlurKernel(src: Img, x: Int, y: Int, radius: Int): RGBA = {
    var colors: List[RGBA] = List()
    for (x_ <- (x-radius) to (x+radius)) {
      for (y_ <- (y-radius) to (y+radius)) {
        if (src.valid_x(x_) && src.valid_y(y_)) {
          colors = src.apply_clamped(x_, y_) :: colors
        }
      }
    }
    avg_rgba(colors)
  }

}
