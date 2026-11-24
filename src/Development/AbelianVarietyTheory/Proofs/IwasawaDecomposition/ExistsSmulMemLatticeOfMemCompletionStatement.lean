module

public import Formalism.LocalRingCardinality.DataLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemLatticeOfMemCompletion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_smul_mem_lattice_of_mem_completion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E M → ∀ z : Fin n → E, (fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈ latS (F := F) (v.adicCompletion F) (intV E v) M → ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) r • z ∈ M := by
  first | exact @GlobalTheory.LatticeDescent.exists_smul_mem_of_mem_latS | exact GlobalTheory.LatticeDescent.exists_smul_mem_of_mem_latS | (intros; apply GlobalTheory.LatticeDescent.exists_smul_mem_of_mem_latS <;> assumption)
