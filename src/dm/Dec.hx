// Copyright 15-Jun-2020 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

package dm;

import dm.Opt;
using StringTools;

///Utilities for managing float numbers.
class Dec {

  static function pow (n: Int) {
    return switch (n) {
      case 0: 1;
      case 1: 10;
      case 2: 100;
      case 3: 1000;
      case 4: 10000;
      case 5: 100000;
      case 6: 1000000;
      case 7: 10000000;
      case 8: 100000000;
      case _: 1000000000;
    }
  }

  static function format (f: Float, scale: Int, thousand: String, dec: String) {
    final parts = to(f, scale).split(".");
    var left = parts[0];
    var end = f < 0 ? left.length - 1 : left.length;
    var cut = 3;
    while (end > cut) {
      final ix = left.length - cut;
      left = left.substring(0, ix) + thousand + left.substring(ix);
      cut += 4;
      ++end;
    }
    return parts.length == 1 ? left : left + dec + parts[1];
  }

  /// Returns 'true' it f2 + dif > f1 > f2 - dif.
  public static function eq (f1: Float, f2: Float, dif: Float): Bool {
    return f1 < f2 + dif && f1 > f2 - dif;
  }

  /// Returns 'f' rounded with 'scale' decimals.
  public static function round (f: Float, scale: Int): Float {
    scale = scale < 0 ? 0 : scale > 9 ? 9 : scale;
    final mul = pow(scale);
    if (f >= 0)
      return Math.fround(f * mul + 0.000000001) / mul;
    return -(Math.fround(-f * mul + 0.000000001) / mul);
  }

  /// Returns a standad representation of 'f' with 'scale' decimal.
  /// For example:
  ///   to(3, 2) -> "3.00"
  ///   to(3.456, 2) -> "3.46"
  ///   to(3.456, 0) -> "3"
  public static function to (f: Float, scale: Int): String {
    final parts = Std.string(round(f, scale)).split(".");
    if (parts.length == 1) {
      return scale == 0
        ? parts[0]
        : (parts[0] + ".").rpad("0", parts[0].length + 1 + scale)
      ;
    }
    return (parts[0] + "." + parts[1]).rpad("0", parts[0].length + 1 + scale);
  }

  /// Returns a standard representation of 'f' wiht 'scale' decimal, using
  /// '.' as thousand separator and ',' as decimal one.
  public static function toIso (f: Float, scale: Int): String {
    return format(f, scale, ".", ",");
  }

  /// Returns a standard representation of 'f' wiht 'scale' decimal, using
  /// ',' as thousand separator and '.' as decimal one.
  public static function toEn (f: Float, scale: Int): String {
    return format(f, scale, ",", ".");
  }

  /// Returns a float from a standard representation of it.
  public static function from (f: String): Option<Float> {
    final r = Std.parseFloat(f);
    return Math.isNaN(r) ? None : Some(r);
  }

  /// Returns a float from a iso representation of it.
  public static function fromIso (f: String): Option<Float> {
    final r = Std.parseFloat(f.replace(".", "").replace(",", "."));
    return Math.isNaN(r) ? None : Some(r);
  }

  /// Returns a float from a english representation of it.
  public static function fromEn (f: String): Option<Float> {
    final r = Std.parseFloat(f.replace(",", ""));
    return Math.isNaN(r) ? None : Some(r);
  }

  /// Returns 'true' if every character of 'n' is a digit ([0-9]).<p>
  /// If n is an empty string, it returns 'true'.
  public static function digits (n: String): Bool {
    return It.fromString(n).every(d -> d >= "0" && d <= "9");
  }

}
