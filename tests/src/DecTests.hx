// Copyright 14-Aug-2019 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

import dm.Test;
import dm.Dec;
import dm.Opt;

class DecTests {

  public static function run() {
    final t = new Test("Dec");

    t.yes(Dec.eq(Dec.round(0, 0), 0, 0.001));
    t.eq(Dec.to(0, 0), "0");
    t.eq(Dec.toInt(0), 0);
    t.eq(Dec.toIso(0, 0), "0");
    t.eq(Dec.toEn(0, 0), "0");
    t.yes(Dec.eq(Opt.get(Dec.from("0")), 0, 0.001));
    t.yes(Dec.eq(Opt.get(Dec.fromIso("0")), 0, 0.001));
    t.yes(Dec.eq(Opt.get(Dec.fromEn("0")), 0, 0.001));

    t.yes(Dec.eq(Dec.round(-0, 0), 0, 0.001));
    t.eq(Dec.to(-0, 0), "0");
    t.eq(Dec.toIso(-0, 0), "0");
    t.eq(Dec.toEn(-0, 0), "0");
    t.yes(Dec.eq(Opt.get(Dec.from("-0")), 0, 0.001));
    t.yes(Dec.eq(Opt.get(Dec.fromIso("-0")), 0, 0.001));
    t.yes(Dec.eq(Opt.get(Dec.fromEn("-0")), 0, 0.001));

    t.yes(Dec.eq(Dec.round(-3.25499, 2), -3.25, 0.000001));
    t.eq(Dec.to(-3.25499, 2), "-3.25");
    t.eq(Dec.toIso(-3.25499, 2), "-3,25");
    t.eq(Dec.toEn(-3.25499, 2), "-3.25");
    t.yes(Dec.eq(Opt.get(Dec.from("-3.25499")), -3.25499, 0.000001));
    t.yes(Dec.eq(Opt.get(Dec.fromIso("-3,25499")), -3.25499, 0.000001));
    t.yes(Dec.eq(Opt.get(Dec.fromEn("-3.25499")), -3.25499, 0.000001));

    t.yes(Dec.eq(Dec.round(3.245, 2), 3.25, 0.000001));
    t.not(Dec.eq(Dec.round(3.245, 2), 3.26, 0.000001));
    t.not(Dec.eq(Dec.round(3.245, 2), 3.24, 0.000001));
    t.eq(Dec.to(3.245, 2), "3.25");
    t.eq(Dec.toIso(3.245, 2), "3,25");
    t.eq(Dec.toEn(3.245, 2), "3.25");
    t.yes(Dec.eq(Opt.get(Dec.from("3.245")), 3.245, 0.000001));
    t.yes(Dec.eq(Opt.get(Dec.fromIso("3,245")), 3.245, 0.000001));
    t.yes(Dec.eq(Opt.get(Dec.fromEn("3.245")), 3.245, 0.000001));

    t.yes(Dec.eq(Dec.round(-3.245, 2), -3.25, 0.000001));
    t.eq(Dec.to(-3.245, 2), "-3.25");
    t.eq(Dec.toIso(-3.245, 2), "-3,25");
    t.eq(Dec.toEn(-3.245, 2), "-3.25");
    t.yes(Dec.eq(Opt.get(Dec.from("-3.245")), -3.245, 0.000001));
    t.yes(Dec.eq(Opt.get(Dec.fromIso("-3,245")), -3.245, 0.000001));
    t.yes(Dec.eq(Opt.get(Dec.fromEn("-3.245")), -3.245, 0.000001));

    t.yes(Dec.eq(Dec.round(1.275, 2), 1.28, 0.000001));
    t.eq(Dec.to(1.275, 2), "1.28");
    t.eq(Dec.toIso(1.275, 2), "1,28");
    t.eq(Dec.toEn(1.275, 2), "1.28");
    t.yes(Dec.eq(Opt.get(Dec.from("1.275")), 1.275, 0.000001));
    t.yes(Dec.eq(Opt.get(Dec.fromIso("1,275")), 1.275, 0.000001));
    t.yes(Dec.eq(Opt.get(Dec.fromEn("1.275")), 1.275, 0.000001));

    t.yes(Dec.eq(Dec.round(0.09, 1), 0.1, 0.000001));
    t.eq(Dec.to(0.09, 1), "0.1");
    t.eq(Dec.toIso(0.09, 1), "0,1");
    t.eq(Dec.toEn(0.09, 1), "0.1");
    t.yes(Dec.eq(Opt.get(Dec.from("0.09")), 0.09, 0.000001));
    t.yes(Dec.eq(Opt.get(Dec.fromIso("0,09")), 0.09, 0.000001));
    t.yes(Dec.eq(Opt.get(Dec.fromEn("0.09")), 0.09, 0.000001));

    t.yes(Dec.eq(Dec.round(1.27499, 2), 1.27, 0.000001));
    t.eq(Dec.to(1.27499, 2), "1.27");
    t.eq(Dec.toIso(1.27499, 2), "1,27");
    t.eq(Dec.toEn(1.27499, 2), "1.27");
    t.yes(Dec.eq(Opt.get(Dec.from("1.27499")), 1.27499, 0.000001));
    t.yes(Dec.eq(Opt.get(Dec.fromIso("1,27499")), 1.27499, 0.000001));
    t.yes(Dec.eq(Opt.get(Dec.fromEn("1.27499")), 1.27499, 0.000001));

    t.yes(Dec.eq(Dec.round(3216234125.124, 2), 3216234125.12, 0.000001));
    t.eq(Dec.to(3216234125.124, 2), "3216234125.12");
    t.eq(Dec.toIso(3216234125.124, 2), "3.216.234.125,12");
    t.eq(Dec.toEn(3216234125.124, 2), "3,216,234,125.12");
    t.yes(Dec.eq(Opt.get(
      Dec.from("3216234125.124")), 3216234125.124, 0.000001));
    t.yes(Dec.eq(Opt.get(
      Dec.fromIso("3.216.234.125,124")), 3216234125.124, 0.000001));
    t.yes(Dec.eq(Opt.get(
      Dec.fromEn("3,216,234,125.124")), 3216234125.124, 0.000001));

    t.yes(Dec.eq(Dec.round(-16234125.124, 2), -16234125.12, 0.000001));
    t.eq(Dec.to(-16234125.124, 2), "-16234125.12");
    t.eq(Dec.toIso(-16234125.124, 2), "-16.234.125,12");
    t.eq(Dec.toEn(-16234125.124, 2), "-16,234,125.12");
    t.yes(Dec.eq(Opt.get(
      Dec.from("-16234125.124")), -16234125.124, 0.000001));
    t.yes(Dec.eq(Opt.get(
      Dec.fromIso("-16.234.125,124")), -16234125.124, 0.000001));
    t.yes(Dec.eq(Opt.get(
      Dec.fromEn("-16,234,125.124")), -16234125.124, 0.000001));

    t.yes(Dec.eq(Dec.round(16234125.124, 0), 16234125, 0.000001));
    t.eq(Dec.to(16234125.124, 0), "16234125");
    t.eq(Dec.toIso(16234125.124, 0), "16.234.125");
    t.eq(Dec.toEn(16234125.124, 0), "16,234,125");
    t.yes(Dec.eq(Opt.get(
      Dec.from("16234125.124")), 16234125.124, 0.000001));
    t.yes(Dec.eq(Opt.get(
      Dec.fromIso("16.234.125,124")), 16234125.124, 0.000001));
    t.yes(Dec.eq(Opt.get(
      Dec.fromEn("16,234,125.124")), 16234125.124, 0.000001));

    t.yes(Dec.eq(Dec.round(16234125.1, 2), 16234125.1, 0.000001));
    t.eq(Dec.to(16234125.1, 2), "16234125.10");
    t.eq(Dec.toIso(16234125.1, 2), "16.234.125,10");
    t.eq(Dec.toEn(16234125.1, 2), "16,234,125.10");
    t.yes(Dec.eq(Opt.get(
      Dec.from("16234125.124")), 16234125.124, 0.000001));
    t.yes(Dec.eq(Opt.get(
      Dec.fromIso("16.234.125,124")), 16234125.124, 0.000001));
    t.yes(Dec.eq(Opt.get(
      Dec.fromEn("16,234,125.124")), 16234125.124, 0.000001));

    t.yes(Dec.eq(Dec.round(16234125, 2), 16234125, 0.000001));
    t.eq(Dec.to(16234125, 2), "16234125.00");
    t.eq(Dec.toIso(16234125, 2), "16.234.125,00");
    t.eq(Dec.toEn(16234125, 2), "16,234,125.00");
    t.yes(Dec.eq(Opt.get(
      Dec.from("16234125")), 16234125, 0.000001));
    t.yes(Dec.eq(Opt.get(
      Dec.fromIso("16.234.125")), 16234125, 0.000001));
    t.yes(Dec.eq(Opt.get(
      Dec.fromEn("16,234,125")), 16234125, 0.000001));

    t.yes(Dec.digits(""));
    t.yes(Dec.digits("153"));
    t.not(Dec.digits("153a"));

    t.log();
  }
}
