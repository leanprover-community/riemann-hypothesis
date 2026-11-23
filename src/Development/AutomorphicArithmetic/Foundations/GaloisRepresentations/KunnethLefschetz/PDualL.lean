module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.dualL_holds :
    UpperTheory.Gal.KunnethLefschetz.DualL := by
  intro l _ k _ _ hl d X p hSP hint R L lam hdet hlam
  obtain ⟨s, c, a, hA⟩ := hdet
  have hprop := hSP.1
  have nd : ∀ (n m : ℤ) (h : n + m = 2 * (d : ℤ)) (y : V l X m),
      (∀ x : V l X n, lam (cupV l X h x y) = 0) → y = 0 := by
    intro n m h y hy
    apply hA m y
    intro t ht
    obtain rfl : c t = n := by omega
    rw [R.comm X m (c t) _ ht h, Units.smul_def, map_zsmul, hy, smul_zero]
  have fd : ∀ n, FiniteDimensional ℚ_[l] (V l X n) := by
    intro n
    classical
    let f : V l X n →ₗ[ℚ_[l]] (Fin s → ℚ_[l]) := LinearMap.pi fun t =>
      if h : n + c t = 2 * (d : ℤ) then lam ∘ₗ (cupV l X h).flip (a t) else 0
    refine FiniteDimensional.of_injective f ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply hA n x
    intro t h
    have := congrFun hx t
    simpa [f, h] using this
  have van : ∀ n, 2 * (d : ℤ) < n → Subsingleton (V l X n) := by
    intro n hn
    have key : ∀ z : V l X n, z = 0 := fun z => hA n z (fun t h => by
      haveI := L.neg X (c t) (by omega)
      rw [Subsingleton.elim (a t) 0]
      simp)
    exact ⟨fun x y => by rw [key x, key y]⟩
  have le : ∀ n m (h : n + m = 2 * (d : ℤ)),
      Module.finrank ℚ_[l] (V l X m) ≤ Module.finrank ℚ_[l] (V l X n) := by
    intro n m h
    haveI := fd n
    haveI := fd m
    have inj : Function.Injective ((cupV l X h).compr₂ lam).flip := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro y hy
      exact nd n m h y (fun x => by simpa using LinearMap.congr_fun hy x)
    have := LinearMap.finrank_le_finrank_of_injective inj
    rwa [Subspace.dual_finrank_eq] at this
  have d0 : Module.finrank ℚ_[l] (V l X 0) ≤ 1 := by
    by_cases hpt : Nonempty (Pt p)
    · obtain ⟨y0⟩ := hpt
      have hcon : ConnectedSpace X :=
        connectedSpace_iff_univ.2 (IrreducibleSpace.isIrreducible_univ _).isConnected
      have inj : Function.Injective (pb l y0.1 0) := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro z hz
        apply L.pts p hprop z
        intro y
        rw [L.conn p hprop hcon z y y0, hz]
      have hsurj : Function.Surjective (LinearMap.toSpanSingleton ℚ_[l] _ (oneV l (S k))) := by
        intro w
        obtain ⟨r, hr, -⟩ := L.line w
        exact ⟨r, hr.symm⟩
      haveI : Module.Finite ℚ_[l] (V l (S k) 0) := Module.Finite.of_surjective _ hsurj
      calc Module.finrank ℚ_[l] (V l X 0) ≤ Module.finrank ℚ_[l] (V l (S k) 0) :=
            LinearMap.finrank_le_finrank_of_injective inj
        _ ≤ 1 := finrank_le_one (oneV l (S k)) (fun w => (L.line w).exists.imp fun r hr => hr.symm)
    · have hz : ∀ z : V l X 0, z = 0 := fun z => L.pts p hprop z (fun y => (hpt ⟨y⟩).elim)
      haveI : Subsingleton (V l X 0) := ⟨fun x y => by rw [hz x, hz y]⟩
      simp [Module.finrank_zero_of_subsingleton]
  obtain ⟨x0, hx0⟩ : ∃ x, lam x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hlam (LinearMap.ext hc)
  have surj : Function.Surjective lam := fun r => ⟨(r / lam x0) • x0, by
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx0]⟩
  haveI := fd (2 * (d : ℤ))
  have hnt : Nontrivial (V l X (2 * (d : ℤ))) := ⟨⟨x0, 0, fun h => hx0 (by rw [h, map_zero])⟩⟩
  have d2 : Module.finrank ℚ_[l] (V l X (2 * (d : ℤ))) = Module.finrank ℚ_[l] ℚ_[l] := by
    rw [Module.finrank_self]
    have h1 := (le 0 (2 * (d : ℤ)) (zero_add _)).trans d0
    have h2 := Module.finrank_pos (R := ℚ_[l]) (M := V l X (2 * (d : ℤ)))
    omega
  have inj : Function.Injective lam := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank d2).2 surj
  refine ⟨fd, van, LinearEquiv.ofBijective lam ⟨inj, surj⟩, fun n m h => ?_⟩
  have htr : ((LinearEquiv.ofBijective lam ⟨inj, surj⟩ : V l X (2 * (d : ℤ)) ≃ₗ[ℚ_[l]] ℚ_[l]) :
      V l X (2 * (d : ℤ)) →ₗ[ℚ_[l]] ℚ_[l]) = lam := LinearMap.ext fun x => rfl
  rw [htr]
  haveI := fd n
  haveI := fd m
  have injf : Function.Injective ((cupV l X h).compr₂ lam).flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact nd n m h y (fun x => by simpa using LinearMap.congr_fun hy x)
  have heq : Module.finrank ℚ_[l] (V l X m) = Module.finrank ℚ_[l] (V l X n →ₗ[ℚ_[l]] ℚ_[l]) := by
    rw [Subspace.dual_finrank_eq]
    exact le_antisymm (le n m h) (le m n (by omega))
  exact ⟨injf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 injf⟩
