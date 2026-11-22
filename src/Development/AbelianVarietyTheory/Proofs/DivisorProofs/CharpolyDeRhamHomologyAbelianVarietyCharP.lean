module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTowerAndHeightEqTwoDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankTheoryMu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamVectorExtension

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DeRhamCharpolyP

theorem charpoly_of_red {R K M V : Type} [CommRing R] [Field K] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] [AddCommGroup V] [Module K V]
    (π : R →+* K) (hπ : Function.Surjective π) (c : ℕ) (hc : (c : K) = 0)
    (red : M →ₛₗ[π] V) (hs : Function.Surjective red) (hk : ∀ m, red m = 0 ↔ ∃ n, m = c • n)
    (φ : Module.End R M) (ψ : Module.End K V) (h : ∀ m, red (φ m) = ψ (red m)) :
    ∃ _ : Module.Finite K V, ψ.charpoly = φ.charpoly.map π := by
  classical
  let b := Module.Free.chooseBasis R M
  let v : Module.Free.ChooseBasisIndex R M → V := fun i => red (b i)
  have hred : ∀ m, red m = ∑ i, π (b.repr m i) • v i := fun m => by
    conv_lhs => rw [← b.sum_repr m]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smulₛₗ red _ _
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    let a : Module.Free.ChooseBasisIndex R M → R := fun j => Function.surjInv hπ (g j)
    have ha : ∀ j, π (a j) = g j := fun j => Function.surjInv_eq hπ (g j)
    have h0 : red (∑ j, a j • b j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp_rw [map_smulₛₗ, ha]
      exact hg
    obtain ⟨n, hn⟩ := (hk _).1 h0
    have hai : a i = (c : R) * b.repr n i := by
      have := congrArg (fun m => b.repr m i) hn
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
          Module.Basis.repr_self, smul_eq_mul, map_nsmul] at this
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj])
        (fun hi => absurd (Finset.mem_univ i) hi)] at this
      simpa [nsmul_eq_mul] using this
    rw [← ha i, hai, map_mul, map_natCast, hc, zero_mul]
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    intro x _
    obtain ⟨m, rfl⟩ := hs x
    rw [hred m]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bV : Module.Basis (Module.Free.ChooseBasisIndex R M) K V := Module.Basis.mk hli hsp
  have hbV : ∀ i, bV i = red (b i) := fun i => Module.Basis.mk_apply hli hsp i
  have : Module.Finite K V := Module.Finite.of_basis bV
  refine ⟨this, ?_⟩
  have hmat : LinearMap.toMatrix bV bV ψ = (LinearMap.toMatrix b b φ).map π := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hbV j, ← h, hred]
    have hv : ∀ i', v i' = bV i' := fun i' => (hbV i').symm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hv, map_sum, map_smul, Module.Basis.repr_self, Finsupp.finsetSum_apply,
        Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, mul_ite, _root_.mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← LinearMap.charpoly_toMatrix ψ bV, hmat, Matrix.charpoly_map, LinearMap.charpoly_toMatrix]

theorem charpoly_dualMap {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module.Finite K (Module.Dual K V)] (f : Module.End K V) : (f.dualMap).charpoly = f.charpoly := by
  classical
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis K V),
    ← LinearMap.charpoly_toMatrix f.dualMap (Module.finBasis K V).dualBasis, ← Matrix.charpoly_transpose,
    LinearMap.dualMap_def, LinearMap.toMatrix_transpose, Matrix.transpose_transpose]

end GlobalTheory.DeRhamCharpolyP

namespace GlobalTheory.DeRhamCharpolyP

end GlobalTheory.DeRhamCharpolyP
