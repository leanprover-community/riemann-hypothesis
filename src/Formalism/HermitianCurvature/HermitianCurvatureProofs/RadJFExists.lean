module

public import Formalism.HermitianCurvature.TopDensNonnegOfKappa
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5.Rad

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jf_uEquiv {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : Mx k r) {h h' : Mx k r} (hh : h ∈ UWset k r D.z)
    (hh' : h' ∈ UWset k r D.z') : B.JF D F (h * g * h') = (D.π h).comp ((B.JF D F g).comp (D.π' h')) := by
  have := P.B5.haar_sigmaFinite D.haarW
  have := P.B5.haar_sigmaFinite D.haarN
  have := P.B5.haar_sigmaFinite D.haarW'
  exact bessel_unitary_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F D.z_mem D.z'_mem D.haarN.conc
    D.haarW.conc D.haarW'.conc (fun h₀ hh₀ => D.haarW.left h₀ hh₀) (fun h₀ hh₀ => D.haarW'.left h₀ hh₀)
    (P.conjugation_invariance_every_setting k r Wp Wq D) D.π_rep D.π'_rep g h hh h' hh'

theorem radJFExists : RadJFExists := by
  intro Wp Wq _ _ _ _ _ _ Pa z z' π π' D F _hP hz hz' hπ hπ' hF
  subst hz hz' hπ hπ'
  classical
  let Φf : Fn Pa.k Pa.r (Wq →L[ℂ] Wp) := fun c g =>
    if (c, g) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) c g else 0
  have hsm := sf_resG (jf_smoothLev D F hF.1)
  have hmem : Φf ∈ RadSp Pa.k Pa.r D.z D.z' D.π D.π' := by
    refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
    · show (if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0) = 0
      rw [if_neg (by simpa using hx)]
    · obtain ⟨U, Fe, hU, hxU, hFe, hΦ⟩ := hsm x₀
        ⟨hx₀.1, wCell_mem_omPlus D.z_mem D.z'_mem hx₀.1 hx₀.2.1 hx₀.2.2⟩ hx₀.2.1
      have hV : IsOpen {x : (Fin Pa.r → ℂ) × Mx Pa.k Pa.r | x.1 ∈ OmX Pa.r ∧ 0 < GGl Pa.k Pa.r D.z D.z' x.2} :=
        ((P.Qx3.isOpen_OmX Pa.r).preimage continuous_fst).inter
          (isOpen_lt continuous_const ((P.Qx5.GGl_continuous Pa.k Pa.r D.z D.z').comp continuous_snd))
      refine ⟨U ∩ {x | x.1 ∈ OmX Pa.r ∧ 0 < GGl Pa.k Pa.r D.z D.z' x.2}, Fe, hU.inter hV,
        ⟨hxU, hx₀.1, hx₀.2.2⟩, hFe.mono Set.inter_subset_left, fun x hx hxG => ?_⟩
      have hxD : (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' := ⟨hx.2.1, hxG, hx.2.2⟩
      show (if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0) = _
      rw [if_pos hxD]
      exact hΦ x hx.1 hxG
    · have hx' : (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' := by simpa using hx
      show (if (x.1, h * x.2 * h') ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 (h * x.2 * h') else 0) =
        (D.π h).comp ((if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0).comp (D.π' h'))
      rw [if_pos (domR_uw hx hh hh'), if_pos hx']
      unfold resG
      have e : wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * (h * x.2 * h') =
          h * (wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * x.2) * h' := by
        have hc := P.Qx3.wlist_comm (k := Pa.k) (Fin.last Pa.r) x.1
          ((List.finRange Pa.r).filter fun a => a.val < (Fin.last Pa.r).val)
          (fun a ha => by simpa using (List.mem_filter.1 ha).2) (P.Qx3.uw_glev (Fin.last Pa.r) hh)
        change wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * h = h * wCell Pa.k Pa.r (Fin.last Pa.r) x.1 at hc
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hc, Matrix.mul_assoc h]
      rw [e, jf_uEquiv D F _ hh hh']
      ext v
      simp
  exact ⟨⟨Φf, hmem⟩, fun x hx => by
    show (if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0) = _
    rw [if_pos (by simpa using hx)]⟩

end Formalism.FourierDecayAlt.P5
