import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCNd
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocI
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.IsLocalRingOfComplete

section
noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain Formalism.BasicNotions.Loc TensorProduct

namespace Formalism.L2.Fam.NPC.BaseC

variable {R : Ranks} (H : Host R) (what₂ : Rows.Data R)

instance factRes (w : what₂.places.Pl) : Fact (what₂.places.resChar w).Prime := ⟨what₂.places.resChar_prime w⟩

structure PlEmb where
  emb : ∀ w : what₂.places.Pl, what₂.LL →+* PadicAlgCl (what₂.places.resChar w)
  emb_w : ∀ w (x : what₂.LL), 0 ≤ what₂.places.val w x ↔ ‖emb w x‖ ≤ 1

structure CoefIn where
  E : PlEmb what₂
  Kx : ∀ (_j : ℕ) (w : what₂.places.Pl), FinExt (what₂.places.resChar w)
  hKx : ∀ j w (x : what₂.LL), E.emb w x ∈ (Kx j w).1

variable {what₂} (X : CoefIn what₂)

def OcC (j : ℕ) (w : what₂.places.Pl) : Type := ↥(OL (X.Kx j w))

instance (j w) : CommRing (OcC X j w) := inferInstanceAs (CommRing ↥(OL (X.Kx j w)))
instance (j w) : IsDomain (OcC X j w) := inferInstanceAs (IsDomain ↥(OL (X.Kx j w)))
instance (j w) : IsDiscreteValuationRing (OcC X j w) := inferInstanceAs (IsDiscreteValuationRing ↥(OL (X.Kx j w)))
instance (j w) : Algebra ℤ_[what₂.places.resChar w] (OcC X j w) := inferInstanceAs (Algebra ℤ_[what₂.places.resChar w] ↥(OL (X.Kx j w)))
instance (j w) : Module.Finite ℤ_[what₂.places.resChar w] (OcC X j w) :=
  inferInstanceAs (Module.Finite ℤ_[what₂.places.resChar w] ↥(OL (X.Kx j w)))
instance (j w) : TopologicalSpace (OcC X j w) := inferInstanceAs (TopologicalSpace ↥(OL (X.Kx j w)))
instance (j w) : IsTopologicalRing (OcC X j w) := inferInstanceAs (IsTopologicalRing ↥(OL (X.Kx j w)))

theorem oc_adic (j w) : IsAdic (IsLocalRing.maximalIdeal (OcC X j w)) := Formalism.BasicNotions.Examples₂.LB.OL_adic (X.Kx j w)

theorem oc_complete (j w) : IsAdicComplete (IsLocalRing.maximalIdeal (OcC X j w)) (OcC X j w) :=
  Formalism.L2.G.IntCl.complete ℤ_[what₂.places.resChar w] ℚ_[what₂.places.resChar w] ↥(X.Kx j w).1 inferInstance

def ecC (j : ℕ) (w : what₂.places.Pl) : what₂.LL →+* FractionRing (OcC X j w) :=
  Formalism.BasicNotions.Examples₂.TwB.embF (X.Kx j w) (X.E.emb w) (X.hKx j w)

theorem ecC_w (j : ℕ) (w : what₂.places.Pl) (x : what₂.LL) :
    0 ≤ what₂.places.val w x ↔ ecC X j w x ∈ (algebraMap (OcC X j w) (FractionRing (OcC X j w))).range := by
  rw [X.E.emb_w]
  constructor
  · intro hx
    have hm : Formalism.BasicNotions.Examples₂.TwB.phiL (X.Kx j w) (X.E.emb w) (X.hKx j w) x ∈ OL (X.Kx j w) :=
      (Formalism.BasicNotions.Examples₂.LB.mem_OL (X.Kx j w) _).mpr hx
    exact ⟨⟨_, hm⟩, (Formalism.BasicNotions.Examples₂.LB.toFrac_eq_iff (X.Kx j w) _ ⟨_, hm⟩).mpr rfl⟩
  · rintro ⟨a, ha⟩
    have h1 := (Formalism.BasicNotions.Examples₂.LB.toFrac_eq_iff (X.Kx j w) _ a).mp ha
    have h2 := (Formalism.BasicNotions.Examples₂.LB.mem_OL (X.Kx j w) _).mp a.2
    rw [h1] at h2
    exact h2

instance algLL (j : ℕ) (w : what₂.places.Pl) : Algebra what₂.LL (FractionRing (OcC X j w)) := (ecC X j w).toAlgebra

def VC (j : ℕ) (w : what₂.places.Pl) : Type := FractionRing (OcC X j w) ⊗[what₂.LL] what₂.MtL (what₂.muTw w) j

instance (j w) : AddCommGroup (VC X j w) := inferInstanceAs (AddCommGroup (FractionRing (OcC X j w) ⊗[what₂.LL] what₂.MtL (what₂.muTw w) j))
instance modK (j w) : Module (FractionRing (OcC X j w)) (VC X j w) :=
  inferInstanceAs (Module (FractionRing (OcC X j w)) (FractionRing (OcC X j w) ⊗[what₂.LL] what₂.MtL (what₂.muTw w) j))
instance modO (j w) : Module (OcC X j w) (VC X j w) := Module.compHom (VC X j w) (algebraMap (OcC X j w) (FractionRing (OcC X j w)))
instance towO (j w) : IsScalarTower (OcC X j w) (FractionRing (OcC X j w)) (VC X j w) where
  smul_assoc a k v := by
    change (a • k) • v = algebraMap (OcC X j w) (FractionRing (OcC X j w)) a • (k • v)
    rw [Algebra.smul_def, mul_smul]

def iVC (j : ℕ) (w : what₂.places.Pl) : what₂.MtL (what₂.muTw w) j →ₛₗ[ecC X j w] VC X j w where
  toFun x := (1 : FractionRing (OcC X j w)) ⊗ₜ[what₂.LL] x
  map_add' x y := TensorProduct.tmul_add _ _ _
  map_smul' c x := by
    change (1 : FractionRing (OcC X j w)) ⊗ₜ[what₂.LL] (c • x) = ecC X j w c • ((1 : FractionRing (OcC X j w)) ⊗ₜ[what₂.LL] x)
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul, mul_one]
    rfl

theorem iVC_basis (j : ℕ) (w : what₂.places.Pl)
    (b : Module.Basis (Module.Free.ChooseBasisIndex what₂.LL (what₂.MtL (what₂.muTw w) j)) what₂.LL (what₂.MtL (what₂.muTw w) j)) :
    LinearIndependent (FractionRing (OcC X j w)) (fun a => iVC X j w (b a)) ∧
      Submodule.span (FractionRing (OcC X j w)) (Set.range fun a => iVC X j w (b a)) = ⊤ := by
  have e : (fun a => iVC X j w (b a)) = fun a => b.baseChange (FractionRing (OcC X j w)) a := by
    funext a
    rw [Module.Basis.baseChange_apply]
    rfl
  rw [e]
  exact ⟨(b.baseChange _).linearIndependent, (b.baseChange _).span_eq⟩

end Formalism.L2.Fam.NPC.BaseC
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N Formalism.L2

namespace Formalism.L2.Fam.NPC.BaseC

variable {R : Ranks} (H : Host R) (what₂ : Rows.Data R)

structure MtReal0 (μ : what₂.Tup) (j : ℕ) where
  wt : NG.AlgWt H.E R.nV
  J : Subgroup (GAf H.E R.nV)
  χ : J →* ℂˣ
  J_open : ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong H.E R.nV N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1
  real : what₂.Mt μ j →ₗ[ℂ] (GAf H.E R.nV → wt.W)
  real_inj : Function.Injective real
  real_range : LinearMap.range real = NG.TypeSp wt.ρ J χ

abbrev MtFam0 : Type 1 := ∀ (μ : what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ R.m → MtReal0 H what₂ μ j

variable {H what₂}

def HeckeLift0 (M : MtFam0 H what₂) (Qw : what₂.places.Pl → Finset (HeightOneSpectrum (𝓞 H.E))) : Prop :=
  ∀ (j : ℕ) (w : what₂.places.Pl) (v : HeightOneSpectrum (𝓞 H.E)) (k : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ R.m),
    GenAt0 H (what₂.places.resChar w) (Qw w) v k →
    ∃ T : Module.End what₂.LL (what₂.MtL (what₂.muTw w) j), ∀ (s : SplitPlace H.E)
      (ϖ : HeightOneSpectrum.adicCompletion (↥(maximalRealSubfield H.E)) s.v),
      IsConjPl H v s.w → IsUnif H.E s.v ϖ → ∀ x,
        (M (what₂.muTw w) j h1 h2).real (what₂.jMt (what₂.muTw w) j (T x)) = NG.tN (M (what₂.muTw w) j h1 h2).J s ϖ k ((M (what₂.muTw w) j h1 h2).real (what₂.jMt (what₂.muTw w) j x))

variable (M : MtFam0 H what₂) (Qw : what₂.places.Pl → Finset (HeightOneSpectrum (𝓞 H.E))) (hR : HeckeLift0 M Qw)

open Classical in

def hLC (j : ℕ) (w : what₂.places.Pl) (v : HeightOneSpectrum (𝓞 H.E)) (k : ℕ) :
    Module.End what₂.LL (what₂.MtL (what₂.muTw w) j) :=
  if h : (1 ≤ j ∧ j ≤ R.m) ∧ GenAt0 H (what₂.places.resChar w) (Qw w) v k then (hR j w v k h.1.1 h.1.2 h.2).choose else 0

theorem hLC_spec (j : ℕ) (w : what₂.places.Pl) (v : HeightOneSpectrum (𝓞 H.E)) (k : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ R.m)
    (hg : GenAt0 H (what₂.places.resChar w) (Qw w) v k) (s : SplitPlace H.E)
    (ϖ : HeightOneSpectrum.adicCompletion (↥(maximalRealSubfield H.E)) s.v) (hc : IsConjPl H v s.w) (hu : IsUnif H.E s.v ϖ)
    (x : what₂.MtL (what₂.muTw w) j) :
    (M (what₂.muTw w) j h1 h2).real (what₂.jMt (what₂.muTw w) j (hLC M Qw hR j w v k x)) =
      NG.tN (M (what₂.muTw w) j h1 h2).J s ϖ k ((M (what₂.muTw w) j h1 h2).real (what₂.jMt (what₂.muTw w) j x)) := by
  have h : (1 ≤ j ∧ j ≤ R.m) ∧ GenAt0 H (what₂.places.resChar w) (Qw w) v k := ⟨⟨h1, h2⟩, hg⟩
  unfold hLC
  rw [dif_pos h]
  exact (hR j w v k h.1.1 h.1.2 h.2).choose_spec s ϖ hc hu x

variable (X : CoefIn what₂)

def hKC (j : ℕ) (w : what₂.places.Pl) (v : HeightOneSpectrum (𝓞 H.E)) (k : ℕ) :
    Module.End (FractionRing (OcC X j w)) (VC X j w) :=
  (hLC M Qw hR j w v k).baseChange (FractionRing (OcC X j w))

theorem hKC_def (j : ℕ) (w : what₂.places.Pl) (v : HeightOneSpectrum (𝓞 H.E)) (k : ℕ) (x : what₂.MtL (what₂.muTw w) j) :
    hKC M Qw hR X j w v k (iVC X j w x) = iVC X j w (hLC M Qw hR j w v k x) :=
  LinearMap.baseChange_tmul _ _ _

def SplitK : Prop :=
  ∀ j w v k, GenAt0 H (what₂.places.resChar w) (Qw w) v k → ⨆ μ, (hKC M Qw hR X j w v k).maxGenEigenspace μ = ⊤

def baseC (hS : SplitK M Qw hR X) : LocBase0 H what₂ where
  Oc := OcC X
  Oc_adic := oc_adic X
  Oc_complete := oc_complete X
  ec := ecC X
  ec_w := ecC_w X
  V := VC X
  iV := iVC X
  iV_basis := iVC_basis X
  Qw := Qw
  hL := hLC M Qw hR
  hK := hKC M Qw hR X
  hK_def := hKC_def M Qw hR X
  split := hS


end Formalism.L2.Fam.NPC.BaseC
end
end
