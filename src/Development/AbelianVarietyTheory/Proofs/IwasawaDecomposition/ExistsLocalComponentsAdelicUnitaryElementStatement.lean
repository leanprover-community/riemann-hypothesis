module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalComponentsAdelicUnitaryElement
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

theorem _root_.GlobalTheory.T.exists_local_components_adelic_unitary_element : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (B : Matrix (Fin (M + 1)) (Fin M) E) (g : HA (AF F) σ J), ∃ (gi : HA (Ainf F) σ J) (gv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J), projInf (g • ratTup (F := F) (AF F) x) = gi • ratTup (F := F) (Ainf F) x ∧ (∀ v, projV v (projFin (g • ratTup (F := F) (AF F) x)) = gv v • ratTup (F := F) (Fv F v) x) ∧ (∀ y y', projInf (pairOf (AF F) σ J B y g y') = pairOf (Ainf F) σ J B (projInf y) gi (projInf y')) ∧ (∀ v y y', projV v (projFin (pairOf (AF F) σ J B y g y')) = pairOf (Fv F v) σ J B (projV v (projFin y)) (gv v) (projV v (projFin y'))) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, (HA.mat (Fv F v) σ J (gv v)).val i j ∈ intV b v ∧ (HA.mat (Fv F v) σ J ((gv v))⁻¹).val i j ∈ intV b v := by
  first | exact @GlobalTheory.GaugeEx.LocComp.exists_local_components | exact GlobalTheory.GaugeEx.LocComp.exists_local_components | (intros; apply GlobalTheory.GaugeEx.LocComp.exists_local_components <;> assumption)
