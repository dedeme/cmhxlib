// Copyright 15-Jun-2020 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

package dm;

import haxe.PosInfos;

/// Exceptions management.
class Exc {

  static function show (msg: String, pos: PosInfos): String {
    return '${pos.fileName}.${pos.methodName}:${pos.lineNumber}: $msg';
  }

  /// Generic exception.
  /// NOTE: It must be thrown with 'throw Exc.generic("Message")'.
  public static function generic (msg: String, ?pos: PosInfos): String {
    return show('Exception : $msg', pos);
  }

  /// Generic exception.
  /// NOTE: It must be thrown with 'throw Exc.generic("Message")'.
  public static function illegalState (msg: String, ?pos: PosInfos): String {
    return show('Illegal state : $msg', pos);
  }

  /// Generic exception.
  /// NOTE: It must be thrown with 'throw Exc.generic("Message")'.
  public static function range (
    begin: Int, end: Int, index: Int, ?pos: PosInfos
  ): String {
    return show('Index out of range : $index out of [$begin - $end]', pos);
  }

  /// Generic exception.
  /// NOTE: It must be thrown with 'throw Exc.generic("Message")'.
  public static function illegalArgument<T> (
    argumentName:String, expected:T, actual:T, ?pos:PosInfos
  ): String {
    return show(
      'Illegal argument : Variable "$argumentName"\n' +
      'Expected: ${Std.string(expected)}\nActual: ${Std.string(actual)}',
      pos
    );
  }

  /// Generic exception.
  /// NOTE: It must be thrown with 'throw Exc.generic("Message")'.
  public static function io (msg: String, ?pos: PosInfos): String {
    return show('IO error : $msg', pos);
  }

  /// Returns the type of a message exception.
  public static function type (msg: String): EType {
    return
        msg.indexOf(": Exception :") != -1 ? EGeneric
      : msg.indexOf(": Illegal state :") != -1 ? EIllegalState
      : msg.indexOf(": Index out of range :") != -1 ? ERange
      : msg.indexOf(": Illegal argument :") != -1 ? EIllegalArgument
      : msg.indexOf(": IO error :") != -1 ? EIo
      : EUndefined
    ;
  }

}

/// Exception types.
enum EType {
  EUndefined;
  EGeneric;
  EIllegalState;
  ERange;
  EIllegalArgument;
  EIo;
}
