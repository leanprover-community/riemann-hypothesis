module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.EulerTw.IntRead

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def thAt (u : Pl E) : GLw n (cPl E u) →* GLw n u :=
  (MulAut.conj (PhiU n (u.adicCompletion E))).toMonoidHom.comp
    ((invT n (u.adicCompletion E)).comp (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv u)))

theorem thAt_apply (u : Pl E) (h : GLw n (cPl E u)) (i j : Fin n) :
    (thAt u h).val i j =
      (-1) ^ ((i : ℕ) + j) * conjLoc (IsCMField.complexConj E).toRingEquiv u ((h⁻¹).val j.rev i.rev) :=
  GlobalTheory.ThetaPull.phi_mul_apply _ i j

theorem map_thF (u : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    GeneralLinearGroup.map (pLoc E u) (thF E n g) = thAt u (GeneralLinearGroup.map (pLoc E (cPl E u)) g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h := GlobalTheory.ThetaPull.thetaGL_apply (a := n) (conjFin (IsCMField.complexConj E).toRingEquiv) g i j
  change pLoc E u ((thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) g).val i j) = _
  rw [h, thAt_apply, map_mul, map_pow, map_neg, map_one, pLoc_conjFin]
  rfl

theorem mem_KGL_of_thAt (u : Pl E) (k : GLw n (cPl E u)) (hk : thAt u k ∈ GlobalTheory.LFun.KGL u (n := n)) :
    k ∈ GlobalTheory.LFun.KGL (cPl E u) (n := n) := by
  have hv : ∀ (h : GLw n (cPl E u)) (i j : Fin n),
      Valued.v ((thAt u h).val i j) = Valued.v ((h⁻¹).val j.rev i.rev) := by
    intro h i j
    rw [thAt_apply, Valuation.map_mul, Valuation.map_pow, Valuation.map_neg, Valuation.map_one, one_pow, one_mul]
    exact (conjLoc_spec (IsCMField.complexConj E).toRingEquiv u).2.2 _
  rw [GlobLev.mem_KGL_iff_val] at hk ⊢
  obtain ⟨h1, h2⟩ := hk
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have := h2 j.rev i.rev
    rw [← map_inv, hv, inv_inv, Fin.rev_rev, Fin.rev_rev] at this
    exact this
  · have := h1 j.rev i.rev
    rwa [hv, Fin.rev_rev, Fin.rev_rev] at this

end GlobalTheory.EulerTw.IntRead

namespace GlobalTheory.EulerTw.IntRead

open GlobalTheory.EulerTw

end GlobalTheory.EulerTw.IntRead
