module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import ReciprocityTheory.DualLattices.CokernelLengthComparisonStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAbelianTorusGeneratorsAtPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_abelian_torus_generators_at_place : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (α : ℤ_[p] ⊗[ℤ] OE) (b : Module.Basis (Fin w.n) ℤ_[p] w.Ow), (∀ k, (b k : ℤ_[p] ⊗[ℤ] OE) = w.e * α ^ (k : ℕ)) → ∀ (rp rm : ℕ) (W : Fin w.n → Fin rp → Fin d → O), (∀ j, EigB ρG ((t j : Emb (O := O) w.e) : OE →+* O) (W j)) → (∀ τ ∈ Emb (O := O) w.bar, eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp τ) ≤ rm) → ∃ (h : ℕ) (ψ : Fin h → Fin d → O), h ≤ rp + rm ∧ (∀ l j, Pdiv.ChartF.res (W j) (ψ l) ∈ Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W j) (s k))) ∧ ∃ f : htCoker H w.e w.bar →ₗ[O] ((LinearMap.range (LinearMap.pi fun y : Fin w.n × Fin rp => (LinearMap.proj y.2).comp (Pdiv.ChartF.res (W y.1))) : Submodule O (Fin w.n × Fin rp → O)) ⧸ (Submodule.span O (Set.range fun q : Fin w.n × Fin h => fun y : Fin w.n × Fin rp => tauExt ((t y.1 : Emb (O := O) w.e) : OE →+* O) α ^ (q.1 : ℕ) * Pdiv.ChartF.res (W y.1) (ψ q.2) y.2)).comap (Submodule.subtype _)), Function.Surjective f := by
  first | exact @GlobalTheory.ChF.GenAtPlace.exists_generators | exact GlobalTheory.ChF.GenAtPlace.exists_generators | (intros; apply GlobalTheory.ChF.GenAtPlace.exists_generators <;> assumption)
