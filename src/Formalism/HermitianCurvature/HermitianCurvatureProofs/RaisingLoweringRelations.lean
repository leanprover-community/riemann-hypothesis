module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothOnHOfLoc
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PolyTopOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem raising_lowering_relations : KrAA := by
  intro k r Wp Wq _ _ _ _ _ _ Bs F hF u x hx
  obtain ⟨hs, ⟨R, hR⟩, -⟩ := hF
  exact (PBG.kr_AA_cpt Bs hs (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R)
    (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne)) r le_rfl u 0 hx).1

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

namespace Formalism.FourierDecayAlt.P

theorem polynomial_top : PBN.PolyTop := VandermondePolynomialIntegral.polyTop_of VandermondePolynomialIntegral.raising_lowering_relations

end Formalism.FourierDecayAlt.P
