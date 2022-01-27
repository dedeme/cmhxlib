// Copyright 15-Jun-2020 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

package dm;

import dm.Opt;

/// Utilities for managing dates-times.
/// It is necessary keep in mind that precision in 'c' is of seconds.
class Dt {

  static function froms (s: String, isEn: Bool): Option<Date> {
    var d = s.substring(0, 2);
    var m = s.substring(3, 5);
    if (isEn) {
      final tmp = d;
      d = m;
      m = tmp;
    }
    return from(s.substring(6) + m + d);
  }

  /// Makes a Date. January has value 1.
  public static function mk (day: Int, month: Int, year: Int): Date {
    return new Date(year, month - 1, day, 0, 0, 0);
  }

  /// Returns the day of 'd' [1-31].
  public static function day (d: Date): Int {
    return d.getDate();
  }

  /// Returns the week day of 'd' [0(Sunday)-6].
  public static function weekDay (d: Date): Int {
    return d.getDay();
  }

  /// Returns the month of 'd' [1-12].
  public static function month (d: Date): Int {
    return d.getMonth() + 1;
  }

  /// Returns the year of 'd' (4 digits).
  public static function year (d: Date): Int {
    return d.getFullYear();
  }

  /// Returns 'd' timestamp in seconds.
  public static function timestamp (d: Date): Float {
    return d.getTime() / 1000.0;
  }

  /// Returns 'd1 - d2' in milliseconds.
  public static function dfMillis (d1: Date, d2: Date): Float {
    return d1.getTime() - d2.getTime();
  }

  /// Returns 'dfMillis(d1, d2) == 0' (Compared with dfMillis).
  public static function eqTime (d1: Date, d2: Date): Bool {
    return dfMillis(d1, d2) == 0;
  }

  /// Returns 'dfMillis(d1, d2)' (Compared with dfMilllis).
  public static function compareTime (d1: Date, d2: Date): Int {
    var df = dfMillis(d1, d2);
    return df > 0 ? 1 : df < 0 ? -1 : 0;
  }

  /// Returns 'd1 - d2' in days.
  public static function df (d1: Date, d2: Date): Int {
    return Math.round(dfMillis(
      new Date(d1.getFullYear(), d1.getMonth(), d1.getDate(), 0, 0, 0),
      new Date(d2.getFullYear(), d2.getMonth(), d2.getDate(), 0, 0, 0)
    ) / 86400000.0);
  }

  /// Returns 'df(d1, d2) == 0' (Compare on days).
  public static function eq (d1: Date, d2: Date): Bool {
    return df(d1, d2) == 0;
  }

  /// Returns 'df(d1, d2)' (Compare on days).
  public static function compare (d1: Date, d2: Date): Int {
    return df(d1, d2);
  }

  /// Returns a new date adding 'd.getTime() + millis'.
  /// Only in javascript.
  /// In 'c' there is only precision of seconds!!!.
  public static function addMillis (d: Date, millis: Float): Date {
    return Date.fromTime(d.getTime() + millis);
  }

  /// Returns a new date adding 'd.getTime() + seconds'.
  public static function addSeconds (d: Date, seconds: Float): Date {
    return Date.fromTime(d.getTime() + seconds * 1000.0);
  }

  /// Returns a new date adding 'days' to 'd'.
  public static function add (d: Date, days: Int): Date {
    return Date.fromTime(d.getTime() + cast(days, Float) * 86400000.0);
  }

  /// Returns a representation of 'd' in format "YYYYMMDD".
  public static function to (d: Date): String {
    return DateTools.format(d, "%Y%m%d");
  }

  /// Returns a representation of 'd' in format "DD(sep)MM(sep)YYYY".<p>
  /// If sep is null, it uses the format "DD/MM/YYYY".
  public static function toIso (d: Date, ?sep: String): String {
    sep = sep == null ? "/" : sep;
    return DateTools.format(d, '%d$sep%m$sep%Y');
  }

  /// Returns a representation of 'd' in format "MM(sep)DD(sep)YYYY".<p>
  /// If sep is null, it uses the format "MM/DD/YYYY".
  public static function toEn (d: Date, ?sep: String) {
    sep = sep == null ? "/" : sep;
    return DateTools.format(d, '%m$sep%d$sep%Y');
  }

  /// Return a date from a string in format "YYYYMMDD".
  public static function from (s: String): Option<Date> {
    if (s.length != 8 || !Dec.digits(s))
      return None;

    final y = Std.parseInt(s.substring(0, 4));
    if (y < 1000)
      return None;
    return Some(Dt.mk(
      Std.parseInt(s.substring(6)),
      Std.parseInt(s.substring(4, 6)),
      y
    ));
  }

  /// Return a date from a string in format "DD(sep)MM(sep)YYYY".
  public static function fromIso (s: String): Option<Date> {
    return froms(s, false);
  }

  /// Return a date from a string in format "MM(sep)SS(sep)YYYY".
  public static function fromEn (s: String): Option<Date> {
    return froms(s, true);
  }

  /// Returns a representation of 'd' time in format "HH:MM:SS".
  public static function toTime (d: Date): String {
    return DateTools.format(d, "%H:%M:%S");
  }

  /// Return a date from a string in format "(today)MM:SS:YYYY".
  public static function fromTime (s: String): Option<Date> {
    final parts = s.split(":");
    if (s.length != 8 || parts.length != 3)
      return None;
    if (!Dec.digits(parts[0] + parts[1] + parts[2]))
      return None;

    final today = Date.now();
    return Some(new Date(
      today.getFullYear(), today.getMonth(), today.getDate(),
      Std.parseInt(parts[0]), Std.parseInt(parts[1]), Std.parseInt(parts[2])
    ));
  }

  /// Returns 'true' if 'd' is leap.
  public static function isLeap (y) {
    return ((y % 4 == 0) && (y % 100 != 0)) || (y % 400 == 0);
  }

}

