module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbWords
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocOfSmoothOnH
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialBesselSmoothCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothLevOfLoc
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselWordSmoothness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBQ

def ProperDomPH : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (Cs : Set (B.Mat P.k P.r)), IsCompact Cs →
    PartialBesselProperness.Proper (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) Cs (domP P.k P.r j p.T.base.z p.T.base.z')

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem smooth_pbT (hP : ProperDomPH) (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (j : ℕ) (hj : j ≤ P.r) (hF : KB.CptCoef p.T.base F) :
    Q.SmoothLev P.k P.r 0 (domP P.k P.r j p.T.base.z p.T.base.z') (pbT p j hj F) := by
  obtain ⟨hck, ⟨R, hR⟩, -⟩ := hF
  have hCs : IsCompact {g : B.Mat P.k P.r | B.gN g ≤ R} := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R
  have hz : ∀ g ∈ B.GV P.k P.r, g ∉ {g : B.Mat P.k P.r | B.gN g ≤ R} → F g = 0 := fun g hg hgC => by
    by_contra h; exact hgC (hR g hg h)
  have hzl : p.T.base.z = D.castV (by omega : j + (P.r - j) = P.r) (liftVec P.k j (P.r - j) (p.T.bs j).z) :=
    (p.T.z_lev j hj).symm
  refine Formalism.FourierDecayAlt.P.PBG.smoothLev_of_loc fun x hx => ?_
  exact Formalism.FourierDecayAlt.P.partial_bessel_smooth_compact_support P.k j (P.r - j) P.r Wp Wq (p.T.bs j) p.T.base (by omega) hzl F _ hck hCs hz
    _ (isOpen_domP P.k P.r j p.T.base.z p.T.base.z') (hP Wp Wq P p j hj _ hCs) x hx.2 hx.1.1

theorem word_smooth_partial_bessel_induction (hP : ProperDomPH) (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (j : ℕ) (hj : j + 1 ≤ P.r) (hF : KB.CptCoef p.T.base F) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)),
      Q.SmoothLev P.k P.r 0 (domP P.k P.r j p.T.base.z p.T.base.z')
        (D.uwG P.k P.r p.T.base.z p.T.base.z' (pbT p j (by omega) F) j (by omega) w e)
  | [], _ => smooth_pbT hP P p F j (by omega) hF
  | l :: w, e => by
    show Q.SmoothLev P.k P.r 0 _ (D.vLet P.k P.r p.T.base.z p.T.base.z' j (by omega) l (e 0)
      (D.uwG P.k P.r p.T.base.z p.T.base.z' (pbT p j (by omega) F) j (by omega) w fun a => e a.succ))
    exact Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts.smooth_vLet _ _ j (by omega) l (e 0) (isOpen_domP P.k P.r j p.T.base.z p.T.base.z')
      (word_smooth_partial_bessel_induction hP P p F j hj hF w _) (fun g hg => hg.1 ⟨j, by omega⟩ (show j ≤ j from le_rfl) (show j ≤ P.r by omega))

end

theorem wordSmooth_of (hP : ProperDomPH) : CutHB.WordSmooth := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w hF _ e
  exact word_smooth_partial_bessel_induction hP P p F j hj hF w e

end Formalism.FourierDecayAlt.P.PartialBesselWordSmoothness
