module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveLocBOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramLocSetCApp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralBoundOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftLocalPositiveCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositivityBoundOfActual
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThresholdsPositive
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveLocalPositiveCompactSupport
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

namespace Formalism.FourierDecayAlt.P.PBASM

open Formalism.FourierDecayAlt NumberField

noncomputable section

theorem waveLocB_of_cpt (hPSC : P5.ThmPActualCpt → StandardPairingDecay.PStdC) : P5.ThmPActualCpt → WaveLocB := by
  intro hA Cb
  refine ⟨28 * Real.exp 1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB
  exact wave_local_positive_compact_support hA (hPSC hA) Cb _ E Wp Wq S p f χ A₀ le_rfl hB

theorem liftLocB_of_cpt (hDL : KB.DegLift) : P5.ThmPActualCpt → LiftLocB := by
  intro hA Cb
  refine ⟨28 * Real.exp 1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB
  obtain ⟨Λ0, hΛ0, hl⟩ := lift_local_positive_compact_support hA hDL Cb _ E Wp Wq S p f χ A₀ le_rfl hB
  refine ⟨fun b s v => if 1 ≤ b ∧ 1 ≤ s ∧ b + s ≤ S.G.r + 1 then Λ0 b s v else 0, ?_, ?_, ?_⟩
  · intro b s v
    beta_reduce
    by_cases h : 1 ≤ b ∧ 1 ≤ s ∧ b + s ≤ S.G.r + 1
    · rw [if_pos h]; exact (hΛ0 b s h.1 h.2.1 h.2.2 v).1
    · rw [if_neg h]
  · intro b s hb hs hbs v
    beta_reduce
    rw [if_pos ⟨hb, hs, hbs⟩]; exact (hΛ0 b s hb hs hbs v).2
  · intro F hF v b s hb hs hbs
    have h : (if 1 ≤ b ∧ 1 ≤ s ∧ b + s ≤ S.G.r + 1 then Λ0 b s v else 0) = Λ0 b s v := if_pos ⟨hb, hs, hbs⟩
    simp only [h]
    exact hl F hF v b s hb hs hbs

end

def BuiltBounds2CptOfLeaves : Prop :=
  KB.RadHead → KB.HeadTop → KB.DegLift → PBL.TopLocB → KB.DegTop → PBL.TopRatio → GermPartsC →
  (P5.ThmPActualCpt → DecayUnif) → KB.BuiltBounds2Cpt

theorem builtBounds2CptOfLeaves : BuiltBounds2CptOfLeaves := by
  intro hRH hHT hDL hTL hDT hTR hGP hD
  have hPSC : P5.ThmPActualCpt → StandardPairingDecay.PStdC := fun hA => StandardPairingDecay.pStdC_of hA hRH hHT
  have hI : P5.ThmPActualCpt → IntB := fun hA => integral_bound_of_parts (hPSC hA) (hD hA)
  exact builtBounds2CptOfParts (waveLocB_of_cpt hPSC) (liftLocB_of_cpt hDL) hTL (fun _ => hDT)
    (fun _ => vector_valued_types) (fun _ => hTR) (fun hA => germLocB_of (hI hA) hGP) positivity_bound hI hD
    (fun _ => thrPos)

end Formalism.FourierDecayAlt.P.PBASM

namespace Formalism.FourierDecayAlt.P

theorem built_bounds_compact_of_leaves : PBASM.BuiltBounds2CptOfLeaves := PBASM.builtBounds2CptOfLeaves

end Formalism.FourierDecayAlt.P
