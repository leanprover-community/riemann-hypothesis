module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PullCochMemCoboundaries
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechShortExactPullCompatStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafPullConnectingCompatStatement
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Nt2

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison.Om.Cech

private theorem step_naturality {A B A' B' C D C' D' : Type}
    (δ : A ≃ B) (δ' : A' ≃ B') (e : A → C) (e' : A' → C')
    (d : C → D) (d' : C' → D') (p : A → A') (q : B → B')
    (r : C → C') (s : D → D')
    (hδ : ∀ y, q (δ y) = δ' (p y)) (he : ∀ y, e' (p y) = r (e y))
    (hd : ∀ z, s (d z) = d' (r z)) (x : B) :
    d' (e' (δ'.symm (q x))) = s (d (e (δ.symm x))) := by
  obtain ⟨y, rfl⟩ := δ.surjective x
  rw [δ.symm_apply_apply, hδ, δ'.symm_apply_apply, he, hd]

theorem cechHStep_pull' : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) [Injective S.X₂] (hC : IsCechShortExact V S.f.hom S.g.hom) (hI : CechAcyclic S.X₂.obj V)
    (hS' : S'.ShortExact) [Injective S'.X₂] (hC' : IsCechShortExact U S'.f.hom S'.g.hom) (hI' : CechAcyclic S'.X₂.obj U)
    (α : S ⟶ S'.map (push f)) (m : ℕ) (e : cechH S.X₃.obj V (m + 1) ≃+ Sheaf.H.{0} S.X₃ (m + 1))
    (e' : cechH S'.X₃.obj U (m + 1) ≃+ Sheaf.H.{0} S'.X₃ (m + 1))
    (he : ∀ y, e' (cechPullH f α.τ₃.hom V U τ hτ (m + 1) y) = hPull f α.τ₃ (m + 1) (e y))
    (x : cechH S.X₁.obj V (m + 2)),
    cechHEquivStep U hS' hC' hI' m e' (cechPullH f α.τ₁.hom V U τ hτ (m + 2) x) =
      hPull f α.τ₁ (m + 2) (cechHEquivStep V hS hC hI m e x) := by
  intro X Y f κ ι V U τ hτ S S' hS _ hC hI hS' _ hC' hI' α m e e' he x
  have h₁₂ : ∀ (W : (Opens Y)ᵒᵖ) (z : S.X₁.obj.obj W),
      α.τ₂.hom.app W (S.f.hom.app W z) =
        S'.f.hom.app ((Opens.map f).op.obj W) (α.τ₁.hom.app W z) :=
    fun W z => congrArg (fun g : S.X₁ ⟶ (S'.map (push f)).X₂ => g.hom.app W z) α.comm₁₂.symm
  have h₂₃ : ∀ (W : (Opens Y)ᵒᵖ) (z : S.X₂.obj.obj W),
      α.τ₃.hom.app W (S.g.hom.app W z) =
        S'.g.hom.app ((Opens.map f).op.obj W) (α.τ₂.hom.app W z) :=
    fun W z => congrArg (fun g : S.X₂ ⟶ (S'.map (push f)).X₃ => g.hom.app W z) α.comm₂₃.symm
  let δ := hC.deltaEquiv hI m
  let δ' := hC'.deltaEquiv hI' m
  let p := cechPullH f α.τ₃.hom V U τ hτ (m + 1)
  let q := cechPullH f α.τ₁.hom V U τ hτ (m + 2)
  have hδ (y : cechH S.X₃.obj V (m + 1)) : q (δ y) = δ' (p y) := by
    refine QuotientAddGroup.induction_on y fun σ => ?_
    exact GlobalTheory.T.cech_short_exact_pull_compat f V U τ hτ
      (F := S.X₁.obj) (I := S.X₂.obj) (Q := S.X₃.obj)
      (F' := S'.X₁.obj) (I' := S'.X₂.obj) (Q' := S'.X₃.obj)
      hC hC' α.τ₁.hom α.τ₂.hom α.τ₃.hom h₁₂ h₂₃ (m + 1) σ
  exact step_naturality δ.toEquiv δ'.toEquiv e e'
    (H.δ hS (m + 1) (m + 2) rfl) (H.δ hS' (m + 1) (m + 2) rfl)
    p q (hPull f α.τ₃ (m + 1)) (hPull f α.τ₁ (m + 2))
    hδ he (GlobalTheory.T.sheaf_pull_connecting_compat f hS hS' α (m + 1)) x

end CrystallineSemistableComparison.Om.Nt2
