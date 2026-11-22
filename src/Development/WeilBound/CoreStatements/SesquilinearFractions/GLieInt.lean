module

public import Development.WeilBound.CoreStatements.SesquilinearFractions.GLieIntC
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalenceStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOfSmoothStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualFamilyIsBasisStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsActionStatement

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.isogeny_decomposition_product

theorem tan_comp {S : Scheme.{0}} {R : Type} [CommRing R] {A B : Over S} [GrpObj A] [GrpObj B] {x : Sp R ⟶ S}
    (t : epsAt x ⟶ A) (ht : IsTanAt A x t) (g : A ⟶ B) [IsMonHom g] : IsTanAt B x (t ≫ g) := by
  unfold IsTanAt at ht ⊢
  rw [Over.comp_left, ← Category.assoc, ht, ← Over.comp_left, MonObj.one_comp]

theorem one_left {S : Scheme.{0}} {X A : Over S} [GrpObj A] : (1 : X ⟶ A).left = X.hom ≫ η[A].left := by
  rw [Hom.one_def]; simp

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  simp [spMap, ← Spec.map_comp]

theorem bc_one {R V : Type} [CommRing R] [CommRing V] (f : R →+* V) {A : Over (Sp R)} [GrpObj A] :
    spMap (dualMap f) ≫ (1 : epsR R ⟶ A).left = (1 : epsAt (spMap f ≫ 𝟙 (Sp R)) ⟶ A).left := by
  rw [one_left, one_left, ← Category.assoc]
  congr 1
  simp only [Over.mk_hom, Category.comp_id]
  rw [spMap_comp, spMap_comp]
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem bc_eps {R V : Type} [CommRing R] [CommRing V] (f : R →+* V) (N : ℕ) :
    spMap (dualMap f) ≫ spMap (GlobalTheory.CompanionTheory.Ar.epsMul (N : R)) = spMap (GlobalTheory.CompanionTheory.Ar.epsMul (N : V)) ≫ spMap (dualMap f) := by
  rw [spMap_comp, spMap_comp]
  congr 1
  ext a <;> simp [dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]

theorem pow_left {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] (v : epsR R ⟶ A)
    (hv : IsLieBasis ![v]) (N : ℕ) :
    v.left ≫ (𝟙 A ^ N).left = spMap (GlobalTheory.CompanionTheory.Ar.epsMul (N : R)) ≫ v.left := by
  obtain ⟨E, _, _, ⟨M⟩⟩ := lieModel_exists (Sp R) A R (𝟙 (Sp R))
  obtain ⟨b, hb⟩ := basis_of_lieBasis v hv M
  have e1 : toAt v = M.pt (b 0) := Over.OverMorphism.ext (by rw [toAt_left, hb])
  have h := congrArg Over.Hom.left (comp_pow' (toAt v) (𝟙 A) N)
  rw [Category.comp_id, e1, ← pt_nsmul, Over.comp_left, ← e1, toAt_left, ← Nat.cast_smul_eq_nsmul R,
    M.smul, ← e1, toAt_left] at h
  exact h

end PositivityTheory.Xgf.isogeny_decomposition_product

namespace PositivityTheory.Xgf

end PositivityTheory.Xgf

end
