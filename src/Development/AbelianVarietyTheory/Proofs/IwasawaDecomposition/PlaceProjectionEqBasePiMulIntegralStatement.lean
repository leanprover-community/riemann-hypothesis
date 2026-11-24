module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.Columns.RecLevelLocT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionEqBasePiMulIntegral
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

theorem _root_.GlobalTheory.T.placeProjection_eq_basePi_mul_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (v : HeightOneSpectrum (𝓞 F)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F), z ∈ Formalism.L2.Herm.intAf F E → (∀ P ∈ ST, Valued.v (adAt F P z) < 1) → ∃ s ∈ intV E v, prV (E := E) v z = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s := by
  first | exact @GlobalTheory.Mem.Col2.prV_eq_pi_mul | exact GlobalTheory.Mem.Col2.prV_eq_pi_mul | (intros; apply GlobalTheory.Mem.Col2.prV_eq_pi_mul <;> assumption)
