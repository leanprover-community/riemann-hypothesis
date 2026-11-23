module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineSiteZariskiCoveredByAtlas
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsActOfHom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEtaleLiftOfSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowDvdFactorialMul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PreimageOpenTopOfJacobsonSurjection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemSpanOfEtale
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubThickOnto
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.elift : ∀ {O R Λ : Type} [CommRing O] [CommRing R] [CommRing Λ] (a : O →+* R) {d : ℕ} (T : Fin d → R) (I : Ideal Λ) (κ : O →+* Λ ⧸ I), (MvPolynomial.eval₂Hom a T).Etale → Nonempty (Lift a T Λ I κ) :=
  @GlobalTheory.CompanionTheory.EtaleLift.nonempty_lift

theorem CrystallineSemistableComparison.B.P.lift_flat : ∀ {Λ D : Type} [CommRing Λ] [CommRing D] (i : Λ →+* D) {d : ℕ} (t : Fin d → D), (MvPolynomial.eval₂Hom i t).Etale → i.Flat ∧ ∀ (J : Ideal D) (μ : D) (g : D →+* D), (∀ x ∈ J, IsNilpotent x) → g.comp i = i → (∀ k, g (t k) - t k ∈ Ideal.span {μ}) → (∀ z, g z - z ∈ J) → ∀ z, g z - z ∈ Ideal.span {μ} :=
  @GlobalTheory.CompanionTheory.LiftFlat.lift_flat

theorem CrystallineSemistableComparison.B.P.thick_onto : ∀ {O : Type} [CommRing O] {F : Fn O} (V : F.Sub) (b : Base) (ht : b.t = 1) (κ : O →+* b.R ⧸ b.I), Onto (subThick V b ht κ) fun T => V.In T.y.1.2 :=
  @GlobalTheory.CompanionTheory.ThickSub.subThick_onto

theorem CrystallineSemistableComparison.B.P.thick_zar : ∀ {O : Type} [CommRing O] (F : Fn O) (b : Base) (ht : b.t = 1) (κ : O →+* b.R ⧸ b.I) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) {d : ℕ} (𝒜 : F.Atlas d), b.p ≠ 0 → ∀ r : ℕ, ZarCov (pdS (F.cr b ht κ) c r).fn fun T => ∃ α, (𝒜.V α).In T.y.1.2 :=
  @GlobalTheory.CompanionTheory.ThickZar.zarCov_pdS

theorem CrystallineSemistableComparison.B.P.thick_act : ∀ {O : Type} [CommRing O] {F : Fn O} {d : ℕ} (s : F.Small d) {b : Base} (ht : b.t = 1) {κ : O →+* b.R ⧸ b.I} (𝓛 : Lift s.a (fun k => (s.T k : s.R)) b.R b.I κ) (δ : DividedPowers (b.I.map 𝓛.i)) (hδ : IsDPMorphism b.γ δ 𝓛.i) (hp : b.p ≠ 0) (hn : IsNilpotent (b.p : b.R)) (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I), ∃ A : Act (𝟭 _) (thU (F.cr b ht κ) q hq) d (liftObj s ht 𝓛 δ hδ hp hn), ∀ (T : Thick (F.cr b ht κ)) (a : Fin d → (thU (F.cr b ht κ) q hq).U T) (c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T) (k : Fin d), (A.act a c).φ (𝓛.t k) = ((a k).1 : T.B) * c.φ (𝓛.t k) :=
  @GlobalTheory.CompanionTheory.ThickAct.thick_act

theorem CrystallineSemistableComparison.B.P.thick_line : ∀ {O : Type} [CommRing O] (F : Fn O) (b : Base) (ht : b.t = 1) (κ : O →+* b.R ⧸ b.I) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (ρ : ℕ → ℕ) (hρ : Slow ρ) (μ : Λ) (hμ : c μ ∈ b.I) (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (x : b.R), b.p.Prime → (q : b.R) = x ^ b.p → c μ = q - 1 → (∑ i ∈ Finset.range b.p, x ^ i) ∈ b.I → ∀ T : Thick (F.cr b ht κ), ∃ (T₁ : Thick (F.cr b ht κ)) (i : T ⟶ T₁) (η : (thU (F.cr b ht κ) q hq).U T₁), (∀ (T' : Thick (F.cr b ht κ)) (φ : T ⟶ T') (a : (thU (F.cr b ht κ) q hq).U T'), ∃! ψ : T₁ ⟶ T', i ≫ ψ = φ ∧ (thU (F.cr b ht κ) q hq).map ψ η = a) ∧ ∀ g : T₁ ⟶ T₁, i ≫ g = i → (thU (F.cr b ht κ) q hq).map g η = (thU (F.cr b ht κ) q hq).q _ * η → (pdFlt (F.cr b ht κ) c ρ hρ μ hμ).FAcyc i g :=
  @GlobalTheory.CompanionTheory.ThickLine.main

theorem CrystallineSemistableComparison.B.P.atlas : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [Smooth q] [IsSeparated q] [QuasiCompact q], ∃ d, Nonempty ((schFn q).Atlas d) :=
  @GlobalTheory.CompanionTheory.SchAtlas.exists_atlas
