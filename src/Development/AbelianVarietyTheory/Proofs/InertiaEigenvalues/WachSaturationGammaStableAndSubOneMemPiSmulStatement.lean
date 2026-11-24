module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSatMOfSmul
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationGammaStableAndSubOneMemPiSmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.saturation_gamma_stable_of_good : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → (∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), W.γ T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧ ∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), W.γ T₂ x - x ∈ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).map (smulA W T₂ letπ) := by
  first | exact @GlobalTheory.NL.GamSat.wachSaturation_gamma_stable_and_sub_one_mem_pi_smul | exact GlobalTheory.NL.GamSat.wachSaturation_gamma_stable_and_sub_one_mem_pi_smul | (intros; apply GlobalTheory.NL.GamSat.wachSaturation_gamma_stable_and_sub_one_mem_pi_smul <;> assumption)
