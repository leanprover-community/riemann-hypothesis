module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
public import Formalism.LocalToGlobal.HermitianForms.TiedStep
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryDatumLevelPrimeSplitDegreeGramFacts
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

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitaryDatum_levelPrime_split_degree_gram_facts : ∀ (D : D7) (u : D.what₂.Word), SplitsIn D.host.E (D.mem u).A.T ∧ (∀ i, SplitsIn D.host.E (D.host.g i)) ∧ (∀ i, (D.mem u).A.T ≠ D.host.g i) ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧ D.R.N 0 = D.R.k ∧ IsHerm (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ∧ (gramN D 0 (Nat.zero_le _)).det ≠ 0 := by
  first | exact @GlobalTheory.St.G.record_facts | exact GlobalTheory.St.G.record_facts | (intros; apply GlobalTheory.St.G.record_facts <;> assumption)
