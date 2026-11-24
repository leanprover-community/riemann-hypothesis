module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerLatticeFacts
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

theorem _root_.GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), A.AA.FG → A.AA ≠ ⊥ → IsSdLat N → IsSdLat N' → (per A N N').FG ∧ (∀ x : HomE X.E a b, ∃ n : ℕ, 0 < n ∧ (n : X.E) • x ∈ per A N N') ∧ (∀ r : 𝓞 X.E, r ≠ 0 → (smulLat (r : X.E) (per A N N')).toAddSubgroup.relIndex (per A N N').toAddSubgroup ≠ 0) ∧ ∀ P : HeightOneSpectrum (𝓞 X.E), localization₂ P.asIdeal A.AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) → ∀ y : HomE X.E a b, y ∈ localization₂ P.asIdeal (per A N N') ↔ ∀ v ∈ localization₂ P.asIdeal N, y v ∈ localization₂ P.asIdeal N' := by
  first | exact @GlobalTheory.MomT.LatFin.per_lattice_facts | exact GlobalTheory.MomT.LatFin.per_lattice_facts | (intros; apply GlobalTheory.MomT.LatFin.per_lattice_facts <;> assumption)
