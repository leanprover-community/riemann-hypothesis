module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TailProdMulOfLatticeMassMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.tailProd_mul_of_lattice_mass_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n₁ M₁ n₂ M₂ n₃ M₃ : ℕ) (mi : Measure (Fin n₁ → Fin M₁ → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₁ → Fin M₁ → Fv F v ⊗[F] E)) (mi' : Measure (Fin n₂ → Fin M₂ → Ainf F ⊗[F] E)) (mv' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₂ → Fin M₂ → Fv F v ⊗[F] E)) (Nv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₃ → Fin M₃ → Fv F v ⊗[F] E)) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), Conv b mi mv → Conv b mi' mv' → (∀ v ∉ S₀, Nv v (latV b v) = mv v (latV b v) * mv' v (latV b v)) → (Summable fun v => |(Nv v (latV b v)).toReal - 1|) ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S → tailProd b Nv S = tailProd b mv S * tailProd b mv' S := by
  first | exact @GlobalTheory.GaugeEx.tailProd_mul_of_mass_mul | exact GlobalTheory.GaugeEx.tailProd_mul_of_mass_mul | (intros; apply GlobalTheory.GaugeEx.tailProd_mul_of_mass_mul <;> assumption)
