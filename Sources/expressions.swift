import LogicKit

// ================================================= NUMBERS ================================================

// Abstract syntaxes of natural constants:
// n in Nat
// --------
// n -> Nat

let d0 = Value (0)
let d1 = Value (1)
let d2 = Value (2)
let d3 = Value (3)
let d4 = Value (4)
let d5 = Value (5)
let d6 = Value (6)
let d7 = Value (7)
let d8 = Value (8)
let d9 = Value (9)

func toNumber (_ n : Int) -> Term {
    var result = List.empty
    for char in String (n).characters.reversed () {
        switch char {
        case "0":
            result = List.cons (d0, result)
        case "1":
            result = List.cons (d1, result)
        case "2":
            result = List.cons (d2, result)
        case "3":
            result = List.cons (d3, result)
        case "4":
            result = List.cons (d4, result)
        case "5":
            result = List.cons (d5, result)
        case "6":
            result = List.cons (d6, result)
        case "7":
            result = List.cons (d7, result)
        case "8":
            result = List.cons (d8, result)
        case "9":
            result = List.cons (d9, result)
        default:
            assert (false)
        }
    }
    return result
}

/////////////////////////////////////////// List reversing \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

func reverseAcc(_ list: Term, _ acc: Term, _ reversed: Term) -> Goal {
  return
      (list === List.empty && reversed === acc) ||
      freshn { t in
           let head = t ["head"]
           let tail = t ["tail"]
           return list === List.cons(head,tail) &&
         delayed(reverseAcc(tail, List.cons(head, acc), reversed)) }
}

func reverse(_ list: Term, _ reversed: Term) -> Goal {

  return reverseAcc(list, List.empty, reversed)
}
//////////////////////////////////////////////////////////////////////////////////////////////////////

// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§
// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§ Arithmetic: §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§
// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§

// Nat = {0,...,9} and Exp = natural expression

/* =================================================== ADDITION =========================================================== */

// Abstract syntax of addition:
//   lhs, rhs in Exp
// --------------------
//   lhs + rhs in Exp

func add (_ lhs: Term, _ rhs: Term) -> Map {
    return [
      "op"  : Value ("+"),
      "lhs" : lhs,
      "rhs" : rhs,
    ]
}

//  *                *                *                 *                     *

func addDigit (_ lhs: Term, _ rhs: Term, _ result: Term, _ carry: Term) -> Goal {
  return
         // lhs = 0 or rhs = 0
         (lhs === d0 && result === rhs && carry === d0) ||
         (rhs === d0 && result === lhs && carry === d0) ||

         // lhs = 1
         (lhs === d1 && rhs === d1 && result === d2 && carry === d0) ||
         (lhs === d1 && rhs === d2 && result === d3 && carry === d0) ||
         (lhs === d1 && rhs === d3 && result === d4 && carry === d0) ||
         (lhs === d1 && rhs === d4 && result === d5 && carry === d0) ||
         (lhs === d1 && rhs === d5 && result === d6 && carry === d0) ||
         (lhs === d1 && rhs === d6 && result === d7 && carry === d0) ||
         (lhs === d1 && rhs === d7 && result === d8 && carry === d0) ||
         (lhs === d1 && rhs === d8 && result === d9 && carry === d0) ||
         (lhs === d1 && rhs === d9 && result === d0 && carry === d1) ||

         // lhs = 2
         (lhs === d2 && rhs === d1 && result === d3 && carry === d0) ||
         (lhs === d2 && rhs === d2 && result === d4 && carry === d0) ||
         (lhs === d2 && rhs === d3 && result === d5 && carry === d0) ||
         (lhs === d2 && rhs === d4 && result === d6 && carry === d0) ||
         (lhs === d2 && rhs === d5 && result === d7 && carry === d0) ||
         (lhs === d2 && rhs === d6 && result === d8 && carry === d0) ||
         (lhs === d2 && rhs === d7 && result === d9 && carry === d0) ||
         (lhs === d2 && rhs === d8 && result === d0 && carry === d1) ||
         (lhs === d2 && rhs === d9 && result === d1 && carry === d1) ||

         // lhs = 3
         (lhs === d3 && rhs === d1 && result === d4 && carry === d0) ||
         (lhs === d3 && rhs === d2 && result === d5 && carry === d0) ||
         (lhs === d3 && rhs === d3 && result === d6 && carry === d0) ||
         (lhs === d3 && rhs === d4 && result === d7 && carry === d0) ||
         (lhs === d3 && rhs === d5 && result === d8 && carry === d0) ||
         (lhs === d3 && rhs === d6 && result === d9 && carry === d0) ||
         (lhs === d3 && rhs === d7 && result === d0 && carry === d1) ||
         (lhs === d3 && rhs === d8 && result === d1 && carry === d1) ||
         (lhs === d3 && rhs === d9 && result === d2 && carry === d1) ||

         // lhs = 4
         (lhs === d4 && rhs === d1 && result === d5 && carry === d0) ||
         (lhs === d4 && rhs === d2 && result === d6 && carry === d0) ||
         (lhs === d4 && rhs === d3 && result === d7 && carry === d0) ||
         (lhs === d4 && rhs === d4 && result === d8 && carry === d0) ||
         (lhs === d4 && rhs === d5 && result === d9 && carry === d0) ||
         (lhs === d4 && rhs === d6 && result === d0 && carry === d1) ||
         (lhs === d4 && rhs === d7 && result === d1 && carry === d1) ||
         (lhs === d4 && rhs === d8 && result === d2 && carry === d1) ||
         (lhs === d4 && rhs === d9 && result === d3 && carry === d1) ||

         // lhs = 5
         (lhs === d5 && rhs === d1 && result === d6 && carry === d0) ||
         (lhs === d5 && rhs === d2 && result === d7 && carry === d0) ||
         (lhs === d5 && rhs === d3 && result === d8 && carry === d0) ||
         (lhs === d5 && rhs === d4 && result === d9 && carry === d0) ||
         (lhs === d5 && rhs === d5 && result === d0 && carry === d1) ||
         (lhs === d5 && rhs === d6 && result === d1 && carry === d1) ||
         (lhs === d5 && rhs === d7 && result === d2 && carry === d1) ||
         (lhs === d5 && rhs === d8 && result === d3 && carry === d1) ||
         (lhs === d5 && rhs === d9 && result === d4 && carry === d1) ||

         // lhs = 6
         (lhs === d6 && rhs === d1 && result === d7 && carry === d0) ||
         (lhs === d6 && rhs === d2 && result === d8 && carry === d0) ||
         (lhs === d6 && rhs === d3 && result === d9 && carry === d0) ||
         (lhs === d6 && rhs === d4 && result === d0 && carry === d1) ||
         (lhs === d6 && rhs === d5 && result === d1 && carry === d1) ||
         (lhs === d6 && rhs === d6 && result === d2 && carry === d1) ||
         (lhs === d6 && rhs === d7 && result === d3 && carry === d1) ||
         (lhs === d6 && rhs === d8 && result === d4 && carry === d1) ||
         (lhs === d6 && rhs === d9 && result === d5 && carry === d1) ||

         // lhs = 7
         (lhs === d7 && rhs === d1 && result === d8 && carry === d0) ||
         (lhs === d7 && rhs === d2 && result === d9 && carry === d0) ||
         (lhs === d7 && rhs === d3 && result === d0 && carry === d1) ||
         (lhs === d7 && rhs === d4 && result === d1 && carry === d1) ||
         (lhs === d7 && rhs === d5 && result === d2 && carry === d1) ||
         (lhs === d7 && rhs === d6 && result === d3 && carry === d1) ||
         (lhs === d7 && rhs === d7 && result === d4 && carry === d1) ||
         (lhs === d7 && rhs === d8 && result === d5 && carry === d1) ||
         (lhs === d7 && rhs === d9 && result === d6 && carry === d1) ||

         // lhs = 8
         (lhs === d8 && rhs === d1 && result === d9 && carry === d0) ||
         (lhs === d8 && rhs === d2 && result === d0 && carry === d1) ||
         (lhs === d8 && rhs === d3 && result === d1 && carry === d1) ||
         (lhs === d8 && rhs === d4 && result === d2 && carry === d1) ||
         (lhs === d8 && rhs === d5 && result === d3 && carry === d1) ||
         (lhs === d8 && rhs === d6 && result === d4 && carry === d1) ||
         (lhs === d8 && rhs === d7 && result === d5 && carry === d1) ||
         (lhs === d8 && rhs === d8 && result === d6 && carry === d1) ||
         (lhs === d8 && rhs === d9 && result === d7 && carry === d1) ||

         // lhs = 9
         (lhs === d9 && rhs === d1 && result === d0 && carry === d1) ||
         (lhs === d9 && rhs === d2 && result === d1 && carry === d1) ||
         (lhs === d9 && rhs === d3 && result === d2 && carry === d1) ||
         (lhs === d9 && rhs === d4 && result === d3 && carry === d1) ||
         (lhs === d9 && rhs === d5 && result === d4 && carry === d1) ||
         (lhs === d9 && rhs === d6 && result === d5 && carry === d1) ||
         (lhs === d9 && rhs === d7 && result === d6 && carry === d1) ||
         (lhs === d9 && rhs === d8 && result === d7 && carry === d1) ||
         (lhs === d9 && rhs === d9 && result === d8 && carry === d1)
}

func addNumber (_ lhs: Term, _ rhs: Term, _ result: Term) -> Goal {
  return
      (lhs === List.empty && result === rhs) || // (0...0) + (*...*) = (*...*) <=> lhs + rhs = result = rhs
      (rhs === List.empty && result === lhs) || // (*...*) + (0...0) = (*...*) <=> lhs + rhs = result = lhs
      freshn { t in
         let lhead = t ["lhead"]
         let rhead = t ["rhead"]
         let ltail = t ["ltail"]
         let rtail = t ["rtail"]
         let rslt = t ["rslt"]
         let crry = t ["crry"]
         let res = t ["res"]
         let ans = t ["ans"]
         // let cry = t ["cry"]

         return lhs === List.cons(lhead, ltail) && // extract the first digit of lhs
                rhs === List.cons(rhead, rtail) && // extract the first digit of rhs

                addDigit(lhead, rhead, rslt, crry) &&   // add the first digits of lhs and rhs

                delayed(addNumber(ltail, List.cons(crry, List.empty),res)) && // add the carry
                delayed(addNumber(res, rtail, ans)) && // recursive call to add the ltail+carry and rtail

                // or we can add the carry at the end (!not tested!)
                // cry = List.cons(crry,empty)
                // addNumber(res, crry, ans)
                // result === reverse(ans)

                result === List.cons(rslt, ans))
     }
}

// Semantic evaluation of addition:
//     lhs -> lv, rhs -> rv
//        (Nat)      (Nat)
// ----------------------------
//      lhs + rhs -> lv + rv
//                    (Nat)

func evalAdd(_ lhs: Term, _ rhs: Term, _ output: Term) -> Goal {
  return
      freshn { t in
               let reversed_lhs = t ["reversed_lhs"]
               let reversed_rhs = t ["reversed_rhs"]
               let reversed_output = t ["reversed_output"]
               return reverse(lhs, reversed_lhs) &&
                      reverse(rhs, reversed_rhs) &&
                      addNumber(lhs, rhs, reversed_output) &&
                      reverse(reversed_output, output)
              }
}

/* =================================================== SUBTRACTION =========================================================== */

// Abstract syntax of subtraction:
//   lhs, rhs in Exp
// --------------------
//   lhs - rhs in Exp

func subtract (_ lhs: Term, _ rhs: Term) -> Map {
    return [
      "op"  : Value ("-"),
      "lhs" : lhs,
      "rhs" : rhs,
    ]
}

// Semantic evaluation of subtraction:
//     lhs -> lv, rhs -> rv, rv ≤ lv
//        (Nat)      (Nat)    (Nat)
// -----------------------------------
//      lhs - rhs -> lv - rv
//                    (Nat)

// Subtraction is the inverse of addition: lhs - rhs = result <=> lhs = result + rhs
func evalSubtraction (_ lhs: Term, _ rhs: Term, _ result: Term) -> Goal {
  return evalAdd(result, rhs, lhs)
}

/* =================================================== MULTIPLICATION =========================================================== */

// Abstract syntax of multiplication:
//   lhs, rhs in Exp
// --------------------
//   lhs * rhs in Exp

func multiply (_ lhs: Term, _ rhs: Term) -> Map {
    return [
      "op"  : Value ("*"),
      "lhs" : lhs,
      "rhs" : rhs,
    ]
}

// Semantic evaluation of multiplication:
//     lhs -> lv, rhs -> rv
//        (Nat)      (Nat)
// ----------------------------
//      lhs * rhs -> lv * rv
//                    (Nat)

func evalMultipy (_ lhs: Term, _ rhs: Term, _ result: Term) -> Goal {
  return
      // lhs = 1 or rhs = 1, 1*x = x*1 = x
      (lhs === d1 && result === rhs) ||
      (rhs === d1 && result === lhs) ||

      delayed( freshn { v in
                        let rho = v ["rho"]
                        let ans = v ["emp"]
                        return  evalSubtraction(rhs, toNumber(1), rho) &&
                                evalMultipy(lhs,rho, ans) &&
                                evalAdd(lhs, ans, result)
       })
}

/* ====================================================== DIVISION =========================================================== */

// Abstract syntax of division:
//   lhs, rhs in Exp
// --------------------
//   lhs / rhs in Exp

func divide (_ lhs: Trm, _ rhs: Term) -> Map {
    return [
      "op"  : Value ("÷"),
      "lhs" : lhs,
      "rhs" : rhs,
    ]
}

// Semantic evaluation of division:
//     lhs -> lv, rhs -> rv, rv ≠ 0
//        (Nat)      (Nat)    (Nat)
// -----------------------------------
//      lhs / rhs -> lv / rv
//                    (Nat)

// Division is the inverse of multiplication: lhs / rhs = result <=> lhs = result * rhs
func evalDivide (_ lhs: Term, _ rhs: Term, _ result: Term) -> Goal {
  return evalMultipy(result, rhs, result)
}


// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§
// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§ Booleans: §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§
// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§

// Bool = {true, false} and Exp = boolean expression

//Abstract syntaxes of boolean constants:

// -----------
//  t in Bool
let t = Value (true)

// -----------
//  f in Bool
let f = Value (false)

/* =================================================== NOT =========================================================== */

// Abstract syntax of not:
//   of in Bool
// -----------------
//  not(of) in Exp
func not (_ of: Term) -> Map {
    return [
      "op"  : Value ("¬"),
      "term" : b,
    ]
}

//Semantic evaluation of not: (further in the function evalBoolean)

//    of in Exp
// ------------------
//  not(of) in Exp

//    of -> f
// ----------------
//   not(of) -> t

//    of -> t
// ----------------
//   not(of) -> f

/* =================================================== AND =========================================================== */

//   lhs,rhs in Exp
// ---------------------
// lhs and rhs in Exp
func and (_ lhs: Term, _ rhs: Term) -> Map {
    return [
      "op"  : Value ("∧"),
      "lhs" : lhs,
      "rhs" : rhs,
    ]
}

// Semantic evaluation of and: (further in the function evalBoolean)

//    lhs,rhs in Exp
// ---------------------
//  lhs and rhs in Exp

//    lhs -> t, rhs -> t
// -----------------------
//     lhs and rhs -> t

//         lhs -> f
// -----------------------
//     lhs and rhs -> f

//         rhs -> f
// -----------------------
//     lhs and rhs -> f

/* ====================================================== OR =========================================================== */

//   lhs,rhs in Exp
// --------------------
// lhs or rhs in Exp
func or (_ lhs: Term, _ rhs: Term) -> Map {
    return [
      "op"  : Value ("∨"),
      "lhs" : lhs,
      "rhs" : rhs,
    ]
}

// Semantic evaluation of or: (further in the function evalBoolean)

//    lhs,rhs in Exp
// ---------------------
//   lhs or rhs in Exp

//    lhs -> t, rhs -> t
// -----------------------
//     lhs or rhs -> t

//    lhs -> f, rhs -> f
// -----------------------
//     lhs or rhs -> f

//   lhs -> f, rhs -> t
// -----------------------
//     lhs or rhs -> t

//    lhs -> t, rhs -> f
// ------------------------
//     lhs or rhs -> t

/* ==================================================== IMPLIES =========================================================== */

//   lhs,rhs in Exp
// --------------------
// lhs => rhs in Exp
func implies (_ lhs: Term, _ rhs: Term) -> Map {
    return [
      "op"  : Value ("⇒"),
      "lhs" : lhs,
      "rhs" : rhs,
    ]
}

// Semantic evaluation of implies: (further in the function evalBoolean)

//       lhs,rhs in Exp
// --------------------------
//   lhs implies rhs in Exp

//     lhs -> t, rhs -> t
// ---------------------------
//     lhs implies rhs -> t

//     lhs -> f, rhs -> f
// -------------------------
//    lhs implies rhs -> f

//   lhs -> f, rhs -> t
// --------------------------
//     lhs implies rhs -> t

//    lhs -> t, rhs -> f
// ------------------------
//   lhs implies rhs -> f

// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§
// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§ Comparisons*: §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§
// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§
// *for naturals
// Exp = natural expression

/* =================================================== LESS THAN =========================================================== */

// Abstract syntax for less than:

//  lhs,rhs in Exp
// ------------------
//  lhs < rhs in Exp

func lessthan (_ lhs: Term, _ rhs: Term) -> Map {
    return [
      "op"  : Value ("<"),
      "lhs" : lhs,
      "rhs" : rhs,
    ]
}

// Semantic evaluation for less than:
//     lhs -> lv, rhs -> rv
//        (Nat)      (Nat)
// ----------------------------
//     lhs < rhs -> lv < rv
//             (Bool)  (Nat)

/* =================================================== LESS OR EQUAL =========================================================== */

// Abstract syntax for less or equal than:

//  lhs,rhs in Exp
// ------------------
//  lhs ≤ rhs in Exp

func lessequal (_ lhs: Term, _ rhs: Term) -> Map {
    return [
      "op"  : Value ("≤"),
      "lhs" : lhs,
      "rhs" : rhs,
    ]
}

// Semantic evaluation for less or equal than:
//     lhs -> lv, rhs -> rv
//        (Nat)      (Nat)
// ----------------------------
//      lhs ≤ rhs -> lv ≤ rv
//             (Bool)  (Nat)

// (Since functions return true or false we don't need a parameter 'result' to verify we receive true from the comparison)
func lessthanDigit (_ lhs: Term, _ rhs: Term) -> Goal {
  return
      // lhs = 0
      (lhs === d0 && rhs === d1) ||
      (lhs === d0 && rhs === d2) ||
      (lhs === d0 && rhs === d3) ||
      (lhs === d0 && rhs === d4) ||
      (lhs === d0 && rhs === d5) ||
      (lhs === d0 && rhs === d6) ||
      (lhs === d0 && rhs === d7) ||
      (lhs === d0 && rhs === d8) ||
      (lhs === d0 && rhs === d9) ||

      // lhs = 1
      (lhs === d1 && rhs === d2) ||
      (lhs === d1 && rhs === d3) ||
      (lhs === d1 && rhs === d4) ||
      (lhs === d1 && rhs === d5) ||
      (lhs === d1 && rhs === d6) ||
      (lhs === d1 && rhs === d7) ||
      (lhs === d1 && rhs === d8) ||
      (lhs === d1 && rhs === d9) ||

      // lhs = 2
      (lhs === d2 && rhs === d3) ||
      (lhs === d2 && rhs === d4) ||
      (lhs === d2 && rhs === d5) ||
      (lhs === d2 && rhs === d6) ||
      (lhs === d2 && rhs === d7) ||
      (lhs === d2 && rhs === d8) ||
      (lhs === d2 && rhs === d9) ||

      // lhs = 3
      (lhs === d3 && rhs === d4) ||
      (lhs === d3 && rhs === d5) ||
      (lhs === d3 && rhs === d6) ||
      (lhs === d3 && rhs === d7) ||
      (lhs === d3 && rhs === d8) ||
      (lhs === d3 && rhs === d9) ||

      // lhs = 4
      (lhs === d4 && rhs === d5) ||
      (lhs === d4 && rhs === d6) ||
      (lhs === d4 && rhs === d7) ||
      (lhs === d4 && rhs === d8) ||
      (lhs === d4 && rhs === d9) ||

      // lhs = 5
      (lhs === d5 && rhs === d6) ||
      (lhs === d5 && rhs === d7) ||
      (lhs === d5 && rhs === d8) ||
      (lhs === d5 && rhs === d9) ||

      // lhs = 6
      (lhs === d6 && rhs === d7) ||
      (lhs === d6 && rhs === d8) ||
      (lhs === d6 && rhs === d9) ||

      // lhs = 7
      (lhs === d7 && rhs === d8) ||
      (lhs === d7 && rhs === d9) ||

      // lhs = 8
      (lhs === d8 && rhs === d9) ||
}

/* =================================================== GREATER THAN =========================================================== */

// Abstract syntax for greater than:

//  lhs,rhs in Exp
// ------------------
//  lhs > rhs in Exp

func greaterthan (_ lhs: Term, _ rhs: Term) -> Map {
    return [
      "op"  : Value (">"),
      "lhs" : lhs,
      "rhs" : rhs,
    ]
}

// Semantic evaluation for greater than:
//     lhs -> lv, rhs -> rv
//        (Nat)      (Nat)
// ----------------------------
//      lhs > rhs -> lv > rv
//             (Bool)  (Nat)

// (Since functions return true or false we don't need a parameter 'result' to verify we receive true from the comparison)
func greaterthanDigit (_ lhs: Term, _ rhs: Term) -> Goal {
  return
      // lhs = 9
      (lhs === d9 && rhs === d0) ||
      (lhs === d9 && rhs === d1) ||
      (lhs === d9 && rhs === d2) ||
      (lhs === d9 && rhs === d3) ||
      (lhs === d9 && rhs === d4) ||
      (lhs === d9 && rhs === d5) ||
      (lhs === d9 && rhs === d6) ||
      (lhs === d9 && rhs === d7) ||
      (lhs === d9 && rhs === d8) ||

      // lhs = 8
      (lhs === d8 && rhs === d0) ||
      (lhs === d8 && rhs === d1) ||
      (lhs === d8 && rhs === d2) ||
      (lhs === d8 && rhs === d3) ||
      (lhs === d8 && rhs === d4) ||
      (lhs === d8 && rhs === d5) ||
      (lhs === d8 && rhs === d6) ||
      (lhs === d8 && rhs === d7) ||

      // lhs = 7
      (lhs === d7 && rhs === d0) ||
      (lhs === d7 && rhs === d1) ||
      (lhs === d7 && rhs === d2) ||
      (lhs === d7 && rhs === d3) ||
      (lhs === d7 && rhs === d4) ||
      (lhs === d7 && rhs === d5) ||
      (lhs === d7 && rhs === d6) ||

      // lhs = 6
      (lhs === d6 && rhs === d0) ||
      (lhs === d6 && rhs === d1) ||
      (lhs === d6 && rhs === d2) ||
      (lhs === d6 && rhs === d3) ||
      (lhs === d6 && rhs === d4) ||
      (lhs === d6 && rhs === d5) ||

      // lhs = 5
      (lhs === d5 && rhs === d0) ||
      (lhs === d5 && rhs === d1) ||
      (lhs === d5 && rhs === d2) ||
      (lhs === d5 && rhs === d3) ||
      (lhs === d5 && rhs === d4) ||

      // lhs = 4
      (lhs === d4 && rhs === d0) ||
      (lhs === d4 && rhs === d1) ||
      (lhs === d4 && rhs === d2) ||
      (lhs === d4 && rhs === d3) ||

      // lhs = 3
      (lhs === d3 && rhs === d0) ||
      (lhs === d3 && rhs === d1) ||
      (lhs === d3 && rhs === d2) ||

      // lhs = 2
      (lhs === d2 && rhs === d0) ||
      (lhs === d2 && rhs === d2) ||

      // lhs = 1
      (lhs === d1 && rhs === d2) ||
}

/* =================================================== GREATER OR EQUAL ========================================================*/

// Abstract syntax for greater or equal than:

//   lhs,rhs in Exp
// ------------------
//  lhs ≥ rhs in Exp

func greaterequal (_ lhs: Term, _ rhs: Term) -> Map {
    return [
      "op"  : Value ("≥"),
      "lhs" : lhs,
      "rhs" : rhs,
    ]
}

// Semantic evaluation for greater or equal than:
//     lhs -> lv, rhs -> rv
//        (Nat)      (Nat)
// ----------------------------
//      lhs ≥ rhs -> lv ≥ rv
//             (Bool)  (Nat)

/* =================================================== EQUAL =========================================================== */

// Abstract syntax for equal to:

//   lhs,rhs in Exp
// ------------------
//  lhs = rhs in Exp

func equal (_ lhs: Term, _ rhs: Term) -> Map {
    return [
      "op"  : Value ("="),
      "lhs" : lhs,
      "rhs" : rhs,
    ]
}

// Semantic evaluation for equal to:
//     lhs -> lv, rhs -> rv
//        (Nat)      (Nat)
// ----------------------------
//      lhs = rhs -> lv = rv
//             (Bool)  (Nat)

func equalDigit (_ lhs: Term, _ rhs: Term, _ result: Term) -> Goal {
  return (lhs === rhs) && (result === t)
}

/* =================================================== NOT EQUAL =========================================================== */

// Abstract syntax for not equal to:

//   lhs,rhs in Exp
// ------------------
//  lhs ≠ rhs in Exp

func notequal (_ lhs: Term, _ rhs: Term) -> Map {
    return [
      "op"  : Value ("≠"),
      "lhs" : lhs,
      "rhs" : rhs,
    ]
}

// Semantic evaluation for not equal to:
//     lhs -> lv, rhs -> rv
//        (Nat)      (Nat)
// ------------------------------
//      lhs ≠ rhs -> lv ≠ rv
//             (Bool)  (Nat)

// Inverse of equal: if equal returns true then notequal must return false
func notequalDigit (_ lhs: Term, _ rhs: Term, _ result: Term) -> Goal {
  return (lhs === rhs) && (result === f)
}

// ================================================================================================================================== \\

func evalEqual (_ lhs: Term, _ rhs: Term) -> Goal {
  return
      (lhs === List.empty && rhs === List.empty) || // lhs = ( ) = ( ) = rhs
      freshn { v in
                 let lhead = v ["lhead"]
                 let rhead = v ["rhead"]
                 let ltail = v ["ltail"]
                 let rtail = v ["rtail"]
                 return
                    lhs === List.cons(lhead, ltail) && rhs === List.cons(rhead, rtail) &&
                    equalDigit(lhead, rhead) &&
                    delayed(evalEqual(ltail, rtail))
      }
}

// func evalNotEqual ...

func evalLessThan(_ lhs : Term,_ rhs : Term) -> Goal {
  return
      freshn { v in
                 let lhead = v ["lhead"]
                 let rhead = v ["rhead"]
                 let ltail = v ["ltail"]
                 let rtail = v ["rtail"]
                 return
                    (lhs === List.empty && rhs === List.cons(rhead, rtail)) || // lhs = ( ) and rhs = (*...*)
                    lessthanDigit(lhs, rhs) ||                                // lhs and rhs are digits
                    // lhs = (*...*) and rhs = (*...*)
                    ((lhs === List.cons(lhead, ltail) && rhs === List.cons(rhead, rtail)) &&
                    ((lessthanDigit(lhead, rhead) && (evalEqual(ltail, rtail) ||
                    delayed(evalLessThan(ltail, rtail)))) ||
                    (greaterEqualDigit(lhead, rhead) && delayed(evalLessThan(ltail, rtail))))
      }
}

func evalGreaterThan(_ lhs : Term,_ rhs : Term, _ result: Term) -> Goal {
  return
      freshn { v in
                 let lhead = v ["lhead"]
                 let rhead = v ["rhead"]
                 let ltail = v ["ltail"]
                 let rtail = v ["rtail"]
                 return
                    (lhs === List.empty && rhs === List.cons(rhead, rtail)) || // lhs = (*...*) and rhs = ( )
                    greaterthanDigit(lhs, rhs) ||                             // lhs and rhs are digits
                    // lhs = (*...*) and rhs = (*...*)
                    ((lhs === List.cons(lhead, ltail) &&
                    rhs === List.cons(rhead, rtail)) &&
                    ((greaterthanDigit(lhead, rhead) && (evalEqual(ltail, rtail) ||
                    delayed(evalGreaterThan(ltail, rtail)))) ||
                    (greaterEqualDigit(lhead, rhead) && delayed(evalGreaterThan(ltail, rtail))))
      }
}

func evalLessEqual(_ lhs : Term,_ rhs : Term) -> Goal {
  return
      evalLessThan(lhs, rhs) ||
      evalEqual(lhs, rhs)
}

func evalGreaterEqual(_ lhs : Term,_ rhs : Term) -> Goal {
  return
      evalGreaterEqualThan(lhs, rhs) ||
      evalEqual(lhs, rhs)
}


// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§
// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§ Evaluation: §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§
// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§

func evalArithmetic (input: Term, output: Term) -> Goal {
  return
      freshn { v in
                 let lhs = v ["lhs"]
                 let rhs = v ["rhs"]
                 let result = v ["result"]
                 return
                    (input === add(lhs, rhs) && evalAdd(lhs, rhs, result) && output === result) ||
                    (input === subtract(lhs, rhs) && evalSubtraction(lhs, rhs, result) && output === result) ||
                    (input === multiply(lhs, rhs) && evalMultiply(lhs, rhs, result) && output === result) ||
                    (input === divide(lhs, rhs) && evalDivide(lhs, rhs, result) && output === result)
      }
}

func evalBoolean (input: Term, output: Term) -> Goal {
  return
        //
        // --------------
        // true -B-> true
        (input === True && output === True) ||
        //
        // --------------
        // false -B-> false
        (input === False && output === False) ||

        //       b -B-> bv
        // --------------------
        //    not(b) -B-> ¬bv
        delayed (freshn { v in
          let b  = v ["b"]
          let bv = v ["bv"]
          return input === not(l, r) &&
                 evalBoolean (l, lv) &&
                 evalBoolean (r, rv) &&
                 (bv === False && output === False) ||
                 (bv === True && output === True)
        })

        // l -B-> lv, r -B-> rv
        // --------------------
        // l and r -B-> lv || rv
        delayed (freshn { v in
          let l  = v ["l"]
          let r  = v ["r"]
          let lv = v ["lv"]
          let rv = v ["rv"]
          return input === and(l, r) &&
                 evalBoolean (l, lv) &&
                 evalBoolean (r, rv) &&
                 (lv === False && rv === False && output === False) ||
                 (lv === True && output === True) ||
                 (rv === True && output === True)
          })

          // l -B-> lv, r -B-> rv
          // --------------------
          // l or r -B-> lv && rv
          delayed (freshn { v in
            let l  = v ["l"]
            let r  = v ["r"]
            let lv = v ["lv"]
            let rv = v ["rv"]
            return input === or(l, r) &&
                   evalBoolean (l, lv) &&
                   evalBoolean (r, rv) &&
                   (lv === True && rv === True && output === True) ||
                   (lv === False && output === False) ||
                   (rv === True && output === False)
          })

          // l -B-> lv, r -B-> rv
          // --------------------
          // l implies r -B-> lv ⇒ rv
          delayed (freshn { v in
            let l  = v ["l"]
            let r  = v ["r"]
            let lv = v ["lv"]
            let rv = v ["rv"]
            return input === implies(l, r) &&
                   evalBoolean (l, lv) &&
                   evalBoolean (r, rv) &&
                   (lv === True && rv === True && output === True) ||
                   (lv === True && rv === False && output === False) ||
                   (lv === False && output === False)
          })
}

func evalComparison (input: Term, output: Term) -> Goal {

}

// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§
// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§ Main evaluation: §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§
// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§

func eval (input: Term, output: Term) -> Goal {
  return
      evalArithmetic(input, output) ||
      evalBoolean(input, output) ||
      evalComparison(input, output)
}
