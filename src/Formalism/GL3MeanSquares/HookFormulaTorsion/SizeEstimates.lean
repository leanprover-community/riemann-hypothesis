import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions

open Finset Filter Topology ArithmeticFunction

noncomputable section

namespace Formalism.HermitianLattices.P.JacobiSumIdentities

private def jHom (q : ℕ) : ℤ →* ℤ where
  toFun a := jacobiSym a q
  map_one' := jacobiSym.one_left q
  map_mul' a b := jacobiSym.mul_left a b q



end Formalism.HermitianLattices.P.JacobiSumIdentities
