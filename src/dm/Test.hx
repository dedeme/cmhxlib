// Copyright 09-Aug-2019 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

package dm;

import haxe.PosInfos;

/// Tests utilities.
class Test {

  final name:String;
  var pass:Int = 0;
  var subName:String = "";


  public function new (name: String) {
    this.name = name;
  }

  function msg<T> (actual: T, expected: T, pos: PosInfos) {
    final m = '${pos.fileName}.${pos.methodName}:${pos.lineNumber}: ' +
      "Test fail in [" + name +
      (subName == "" ? "" : "; ") +
      subName + "]\n" +
      "  Actual  : " + actual + "\n  Expected: " + expected
    ;
    throw new haxe.Exception(m);
  }

  /// Marks a sub-test.
  public function mark (subName: String) {
    this.subName = subName;
  }

  /// Shows a message with the number of passed tests.
  public function log () {
    final m = "Test [" + name + "] summary:\n" + "  Passed: " + pass;
    haxe.Log.trace(m, null);
  }

  /// Tests if 'value' is true.
  public function yes (value: Bool, ?pos: PosInfos) {
    if (value) ++pass;
    else msg(false, true, pos);
  }

  /// Tests if 'value' is false.
  public function not (value: Bool, ?pos: PosInfos) {
    if (value) msg(true, false, pos);
    else ++pass;
  }

  /// Tests if 'actual' is equals to 'expected'
  public function eq<T> (
    actual: T,
    expected: T,
    ?feq: (e1: T, e2: T) -> Bool,
    ?pos: PosInfos
  ) {
    var isEq = feq == null ? actual == expected : feq(actual, expected);
    if (isEq) ++pass;
    else msg(actual, expected, pos);
  }

  /// Tests if 'actual' is not equals to 'expected'
  public function neq<T> (
    actual: T,
    expected: T,
    ?feq: (e1: T, e2: T) -> Bool,
    ?pos: PosInfos
  ) {
    var isEq = feq == null ? actual == expected : feq(actual, expected);
    if (isEq) msg(Std.string(expected), "!= " + expected, pos);
    else ++pass;
  }
}
