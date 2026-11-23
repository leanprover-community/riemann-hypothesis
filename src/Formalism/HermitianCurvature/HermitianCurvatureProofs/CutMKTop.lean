module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMK2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBlockActionInvariant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMTC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkCpt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkTopBump
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

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMK

theorem psi_cast {k a b : ℕ} (e : a = b) (v : Fin (2 * a + k + 1) → ℂ) (c : ℂ) (g : B.Mat k a) :
    psi k b (D.castV e v) c (D.castM e g) = psi k a v c g := by
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

theorem top_construction : TopMk := by
  intro hC Wp Wq _ _ _ _ _ _ P p
  have hT := p.hT
  have hr : P.r ≤ P.r := le_rfl
  have e0 : P.r + (P.r - P.r) = P.r := by omega
  have hρ : P.r - P.r = 0 := Nat.sub_self _
  obtain ⟨b, hbs, hbc, hκL, hκR⟩ := Formalism.FourierDecayAlt.P.CutEX.MkTopBump.bump_exists (k := P.k) (p := P.r) (ρ := P.r - P.r)
    (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).z_mem (p.T.bs P.r).z'_mem
  obtain ⟨β, hβs, hβi, hβK⟩ := Formalism.FourierDecayAlt.P.CutEXMT.top_truncation_construction P.r
  refine ⟨b, b, β, kapL (p.T.bs P.r).z b * kapR (p.T.bs P.r).z' b, hbs, hbc, hbs, hbc, mul_ne_zero hκL hκR, hβs,
    ?_, ?_⟩
  · intro K hK hKU
    obtain ⟨K', hK', hK'1, hK'2⟩ := hβK (Mt P.k (P.r - P.r)) K hK (fun q hq => (hKU hq).1)
    refine ⟨K', hK', fun q hq => ?_, hK'2⟩
    obtain ⟨hd, q₀, hq₀, he⟩ := hK'1 q hq
    exact ⟨hd, he ▸ (hKU hq₀).2⟩
  · intro Φ hΦL hΦU Z y hZ hy
    have hyG : (Matrix.of y : B.Mat P.k (P.r - P.r)) ∈ B.GV P.k (P.r - P.r) :=
      (Formalism.FourierDecayAlt.P.CutEX.MkCptPf.glev_last_iff hρ _).1 hy
    have hz : p.T.base.z' = D.castV e0 (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z') := (p.T.z'_lev P.r hr).symm
    have hpsi : ∀ u : G.UT P.r → ℂ, CutEX.psiU p (G.upper u) =
        psi P.k (P.r + (P.r - P.r)) (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z') cStd
          (U.muP P.k P.r (P.r - P.r) (G.upper u)) := by
      intro u
      unfold CutEX.psiU
      rw [hz]
      exact psi_cast e0 _ _ _
    have key := hC P.k P.r (P.r - P.r) P.r Wp Wq e0 hρ (p.T.bs P.r) p.T.base (p.T.z'_lev P.r hr)
      (p.T.π'_lev P.r hr) (hT P.r hr).1 (hT P.r hr).2.1 (Formalism.FourierDecayAlt.P.PBM.tower_haarW' p.T hT P.r hr e0)
      (hT P.r hr).2.2 (hT 0 (Nat.zero_le _)).2.2 b b β Φ hbs.continuous hbc hbs.continuous hbc Z hZ
      (hβi Z hZ).1 (hβi Z hZ).2 y hyG (fun h1 hh1 h2 hh2 => hΦL Z y hy h1 hh1 h2 hh2)
      (fun u y' hy' => by
        rw [hΦU Z y' (G.upper u) hZ ((Formalism.FourierDecayAlt.P.CutEX.MkCptPf.glev_last_iff hρ _).2 hy')
          (Formalism.FourierDecayAlt.P.LeftFubiniLemmas.upper_isUpUni u), hpsi u])
    exact key

theorem mkTop_of_avgs (hR : RightAvg) (hL : LeftAvg) : CutEX.MkTop := mkTop_of_leaves hR hL top_construction

end Formalism.FourierDecayAlt.P.CutMK
