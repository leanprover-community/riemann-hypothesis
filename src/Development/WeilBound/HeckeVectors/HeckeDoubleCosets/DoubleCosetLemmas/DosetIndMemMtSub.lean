import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.MatchB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeDeterminesSphericalHeckeCharacterGL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeVectorIffInverseDoubleCosetsStatement

noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas.Mch

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.WeylGL
open GlobalTheory.LFun.SatCompare GlobalTheory.CompanionTheory.Ipf.Val
open GlobalTheory.SplitHecke (IntM GInt Hk Reps tr yw nKer)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "𝒪" => HeightOneSpectrum.adicCompletionIntegers K v

theorem heckeVec_central {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {J : Subgroup G}
    {ρ : Representation ℂ G V} {x : V} (hx : x ∈ fixed ρ J) {z : G} (hz : ∀ g, z * g = g * z) :
    heckeVec ρ J (dosetInd ℂ J z) x = ρ z x := by
  rw [heckeVec_dosetInd hx (R := {z}) (by
    intro γ hγ
    rw [Finset.mem_singleton.1 hγ]
    exact mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩) (by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doset.1 hg
    refine ⟨z, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    rw [← hz a, show z⁻¹ * (z * a * b) = a * b by group]
    exact mul_mem ha hb), Finset.sum_singleton]












def theta (m : ℕ) : GL (Fin m) (Cv v) ≃* GL (Fin m) (Cv v) where
  toFun g := tr g⁻¹
  invFun g := tr g⁻¹
  left_inv _ := Units.ext rfl
  right_inv _ := Units.ext rfl
  map_mul' g h := by rw [_root_.mul_inv_rev, GlobalTheory.SplitHecke.tr_mul]

theorem theta_theta {m : ℕ} (g : GL (Fin m) (Cv v)) : theta m (theta m g) = g := Units.ext rfl

theorem theta_mem {m : ℕ} (g : GL (Fin m) (Cv v)) : g ∈ KGL v m ↔ theta m g ∈ KGL v m := by
  rw [mem_KGL, mem_KGL]
  exact (GlobalTheory.SplitHecke.gInt_tr.trans GlobalTheory.SplitHecke.gInt_inv).symm

theorem theta_tor {m : ℕ} {ϖ : Cv v} (h0 : ϖ ≠ 0) (a : Fin m → ℤ) :
    theta m (tor h0 a) = (tor h0 a)⁻¹ := Units.ext (diagonal_transpose _)





theorem exists_sat (m : ℕ) (B : Multiset ℂˣ) (hB : B.card = m) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (ρ : Representation ℂ (GL (Fin m) (Cv v)) V) (x : V), IsSatVecGL v ρ x B := by
  obtain ⟨α, rfl⟩ : ∃ α : Fin m → ℂˣ, Finset.univ.val.map α = B := by
    obtain ⟨l, rfl⟩ := Quot.exists_rep B
    obtain rfl : l.length = m := hB
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  obtain ⟨x, hx⟩ := (hasSatGL_psFunGL (w := v) α).exists_vec
  exact ⟨_, _, _, _, x, hx⟩

theorem hecke_eq_sum {m : ℕ} {ϖ : Cv v} (hu : IsUnifV K v ϖ) (h0 : ϖ ≠ 0)
    {f : GL (Fin m) (Cv v) → ℂ} (hf : f ∈ Hecke ℂ (KGL v m)) :
    ∃ (I : Finset (Fin m → ℤ)) (a : (Fin m → ℤ) → ℂ),
      f = ∑ e ∈ I, a e • dosetInd ℂ (KGL v m) (tor h0 e) := by
  have : f ∈ Submodule.span ℂ (Set.range fun e : Fin m → ℤ => dosetInd ℂ (KGL v m) (tor h0 e)) :=
    mem_of_supp _ hf fun g _ => by
      obtain ⟨a, -, hg⟩ := cartan h0 hu g
      rw [dosetInd_congr hg]
      exact Submodule.subset_span ⟨a, rfl⟩
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 this
  exact ⟨a.support, a, ha.symm⟩




end CompanionTheory.D.Upq.DoubleCosetLemmas.Mch

end
