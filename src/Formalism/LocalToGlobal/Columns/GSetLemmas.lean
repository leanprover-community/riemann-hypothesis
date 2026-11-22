module

public import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
public import Formalism.ThetaLiftIndependence.Statement
public import Formalism.GL3MeanSquares.HookFormulaTorsion.DoubleCosetDecompositionAll

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.DivisionValues Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace GSD

variable (S : GSD K)

theorem wt_eq (h : S.Ok) (s : S.Sec) (c : S.Cl) :
    (S.toCSDOf h s).wt c = Nat.card (MulAction.stabilizer S.G (s.rep c)) := by
  unfold CSD.wt
  exact Fintype.card_eq_nat_card

theorem card_stab_smul (g : S.G) (d : S.D) :
    Nat.card (MulAction.stabilizer S.G (g • d)) = Nat.card (MulAction.stabilizer S.G d) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨g⁻¹ * (x : S.G) * g, ?_⟩
      invFun := fun y => ⟨g * (y : S.G) * g⁻¹, ?_⟩
      left_inv := fun x => ?_
      right_inv := fun y => ?_ }
  · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, MulAction.mem_stabilizer_iff.mp x.2, inv_smul_smul]
  · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul, MulAction.mem_stabilizer_iff.mp y.2]
  · exact Subtype.ext (by simp [mul_assoc])
  · exact Subtype.ext (by simp [mul_assoc])

theorem ipOf_eq_sum (h : S.Ok) (s : S.Sec) (φ ψ : S.D → S.V) :
    S.ipOf h s φ ψ = letI := h.fintypeCl
      ∑ c : S.Cl, ((Nat.card (MulAction.stabilizer S.G (s.rep c)) : K))⁻¹ * S.pair (φ (s.rep c)) (ψ (s.rep c)) := by
  unfold ipOf CSD.csum
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [S.wt_eq h s c]

theorem mem_intOf_iff (N : S.D → Submodule (𝓞 K) S.V)
    (hN : ∀ (g : S.G) (d : S.D), N (g • d) = (N d).map ((S.ρ g).restrictScalars (𝓞 K))) (s : S.Sec)
    (φ : S.EqFun) : φ ∈ S.intOf N ↔ ∀ c, (φ : S.D → S.V) (s.rep c) ∈ N (s.rep c) := by
  constructor
  · intro hφ c
    exact hφ (s.rep c)
  · intro hφ d
    have e := s.mv_smul d
    rw [← e, φ.2, hN]
    exact Submodule.mem_map_of_mem (hφ (S.cls d))

theorem mem_intNab_iff (h : S.Ok) (s : S.Sec) (φ : S.EqFun) :
    φ ∈ S.intNab ↔ ∀ c, (φ : S.D → S.V) (s.rep c) ∈ S.Nab (s.rep c) := by
  exact S.mem_intOf_iff S.Nab h.nab_smul s φ

theorem mem_intDel_iff (h : S.Ok) (s : S.Sec) (φ : S.EqFun) :
    φ ∈ S.intDel ↔ ∀ c, (φ : S.D → S.V) (s.rep c) ∈ S.Del (s.rep c) := by
  exact S.mem_intOf_iff S.Del h.del_smul s φ

def coordOf (h : S.Ok) (s : S.Sec) : S.EqFun ≃ₗ[K] (Fin (S.toCSDOf h s).dim → K) :=
  (S.resOf h s).trans (S.toCSDOf h s).basis.equivFun

theorem I_coordOf (h : S.Ok) (s : S.Sec) (φ : S.EqFun) :
    (S.toCSDOf h s).I (S.coordOf h s φ) = fun c => (φ : S.D → S.V) (s.rep c) := by
  show (((S.toCSDOf h s).basis.equivFun.symm ((S.toCSDOf h s).basis.equivFun (S.resOf h s φ)) :
    (S.toCSDOf h s).Forms) : S.Cl → S.V) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem coordOf_mem_nabLat (h : S.Ok) (s : S.Sec) (φ : S.EqFun) :
    S.coordOf h s φ ∈ (S.toCSDOf h s).nabLat ↔ φ ∈ S.intNab := by
  unfold CSD.nabLat valLatF
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, S.I_coordOf h s φ, Submodule.mem_pi, S.mem_intNab_iff h s φ]
  exact ⟨fun H c => H c (Set.mem_univ c), fun H c _ => H c⟩

theorem map_intNab (h : S.Ok) (s : S.Sec) :
    S.intNab.map ((S.coordOf h s : S.EqFun →ₗ[K] (Fin (S.toCSDOf h s).dim → K)).restrictScalars (𝓞 K)) =
      (S.toCSDOf h s).nabLat := by
  ext x
  constructor
  · intro hx
    obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.mp hx
    exact (S.coordOf_mem_nabLat h s φ).mpr hφ
  · intro hx
    refine Submodule.mem_map.mpr ⟨(S.coordOf h s).symm x, ?_, ?_⟩
    · rw [← S.coordOf_mem_nabLat h s, LinearEquiv.apply_symm_apply]
      exact hx
    · simp

theorem finiteDimensional_EqFun (h : S.Ok) : FiniteDimensional K S.EqFun := by
  letI := h.fintypeCl
  haveI : Module.Finite K S.V := Module.Finite.of_basis S.bV
  exact LinearEquiv.finiteDimensional (S.resOf h S.outSec).symm

variable {S} in
theorem Sec.exists_smul (s s' : S.Sec) (c : S.Cl) : ∃ g : S.G, g • s.rep c = s'.rep c := by
  exact (S.cls_eq_iff _ _).mp ((s'.spec c).trans (s.spec c).symm)

theorem ipOf_indep (h : S.Ok) (s s' : S.Sec) (φ ψ : S.EqFun) : S.ipOf h s φ ψ = S.ipOf h s' φ ψ := by
  rw [S.ipOf_eq_sum h s, S.ipOf_eq_sum h s']
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨g, hg⟩ := Sec.exists_smul s s' c
  rw [← hg, φ.2, ψ.2, h.inv, card_stab_smul]

end GSD

namespace ClsKer

variable {S S' : GSD K} (A : ClsKer S S')

theorem term_smul (φ : S.EqFun) (g : S.G) (d : S.D) (d' : S'.D) :
    A.k (g • d) d' ((φ : S.D → S.V) (g • d)) = A.k d d' ((φ : S.D → S.V) d) := by
  have e1 : ∀ y, S.ρ g⁻¹ (S.ρ g y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have h1 := A.equiv g 1 d d'
  rw [one_smul, map_one] at h1
  rw [h1, φ.2]
  simp only [LinearMap.comp_apply, Module.End.one_apply, e1]

end ClsKer

namespace GSD

variable (S : GSD K)

end GSD

namespace GSD.Iso

variable {S S' : GSD K} (e : GSD.Iso S S')

theorem onCl_cls (d : S.D) : e.onCl (S.cls d) = S'.cls (e.eD d) := rfl

def stabEquiv (d : S.D) : MulAction.stabilizer S.G d ≃ MulAction.stabilizer S'.G (e.eD d) :=
  Equiv.subtypeEquiv e.eG.toEquiv fun g => by
    show g ∈ MulAction.stabilizer S.G d ↔ e.eG g ∈ MulAction.stabilizer S'.G (e.eD d)
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← e.smul, e.eD.apply_eq_iff_eq]

theorem card_stab (d : S.D) :
    Nat.card (MulAction.stabilizer S'.G (e.eD d)) = Nat.card (MulAction.stabilizer S.G d) := by
  exact Nat.card_congr (e.stabEquiv d).symm

theorem iso_onForms_mem_integral_iff (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hc : ∀ d : S.D, N' (e.eD d) = (N d).map ((e.eV : S.V →ₗ[K] S'.V).restrictScalars (𝓞 K))) (φ : S.EqFun) :
    e.onForms φ ∈ S'.intOf N' ↔ φ ∈ S.intOf N := by
  constructor
  · intro hφ d
    have h1 : e.eV ((φ : S.D → S.V) (e.eD.symm (e.eD d))) ∈ N' (e.eD d) := hφ (e.eD d)
    rw [Equiv.symm_apply_apply, hc] at h1
    obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp h1
    have hy' : y = (φ : S.D → S.V) d := e.eV.injective hxy
    rw [← hy']
    exact hy
  · intro hφ d'
    show e.eV ((φ : S.D → S.V) (e.eD.symm d')) ∈ N' d'
    have h2 := hc (e.eD.symm d')
    rw [Equiv.apply_symm_apply] at h2
    rw [h2]
    exact Submodule.mem_map_of_mem (hφ _)

theorem mem_intNab (φ : S.EqFun) : e.onForms φ ∈ S'.intNab ↔ φ ∈ S.intNab := by
  exact e.iso_onForms_mem_integral_iff S.Nab S'.Nab e.nab φ

theorem mem_intDel (φ : S.EqFun) : e.onForms φ ∈ S'.intDel ↔ φ ∈ S.intDel := by
  exact e.iso_onForms_mem_integral_iff S.Del S'.Del e.del φ

def mapSec (s : S.Sec) : S'.Sec where
  rep := fun c' => e.eD (s.rep (e.onCl.symm c'))
  spec := by
    intro c'
    rw [← e.onCl_cls, s.spec, Equiv.apply_symm_apply]

theorem ipOf_onForms (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) (φ ψ : S.EqFun) :
    S'.ipOf h' s' (e.onForms φ) (e.onForms ψ) = S.ipOf h s φ ψ := by
  let _ := h.fintypeCl
  let _ := h'.fintypeCl
  rw [S'.ipOf_indep h' s' (e.mapSec s), GSD.ipOf_eq_sum, GSD.ipOf_eq_sum]
  refine Fintype.sum_equiv e.onCl.symm _ _ fun c' => ?_
  show ((Nat.card (MulAction.stabilizer S'.G (e.eD (s.rep (e.onCl.symm c')))) : K))⁻¹ *
    S'.pair (e.eV ((φ : S.D → S.V) (e.eD.symm (e.eD (s.rep (e.onCl.symm c'))))))
      (e.eV ((ψ : S.D → S.V) (e.eD.symm (e.eD (s.rep (e.onCl.symm c')))))) = _
  rw [e.card_stab, Equiv.symm_apply_apply, e.pair]

end GSD.Iso

namespace LocOp

variable {S S' : GSD K}

end LocOp

namespace GSD

variable (S : GSD K)

@[reducible] def restr (T : SubMulAction S.G S.D) : GSD K where
  G := S.G
  D := T
  V := S.V
  ιV := S.ιV
  bV := S.bV
  pair := S.pair
  ρ := S.ρ
  Nab := fun t => S.Nab (t : S.D)
  Del := fun t => S.Del (t : S.D)

variable (A : Type) [Group A] [MulAction A S.D]

namespace Slice

variable {S A} (σ : S.Slice A)

variable [SMulCommClass A S.G S.D]

end Slice

end GSD

section Fib

variable {G D D₀ : Type} [Group G] [MulAction G D] [MulAction G D₀] (pr : D → D₀)
  (hpr : ∀ (g : G) (d : D), pr (g • d) = g • pr d)

def fibre (x : D₀) : SubMulAction (MulAction.stabilizer G x) D where
  carrier := {d | pr d = x}
  smul_mem' := by
    intro γ d hd
    show pr ((γ : G) • d) = x
    rw [hpr, show pr d = x from hd]
    exact γ.2

def orbitsFib (rep : MulAction.orbitRel.Quotient G D₀ → D₀)
    (hrep : ∀ c, (Quotient.mk'' (rep c) : MulAction.orbitRel.Quotient G D₀) = c) :
    (Σ c : MulAction.orbitRel.Quotient G D₀,
      MulAction.orbitRel.Quotient (MulAction.stabilizer G (rep c)) (fibre pr hpr (rep c))) ≃
      MulAction.orbitRel.Quotient G D :=
  Equiv.ofBijective
    (fun p => Quotient.map' (s₂ := MulAction.orbitRel G D) (fun y : fibre pr hpr (rep p.1) => (y : D))
      (by
        rintro y y' ⟨γ, hγ⟩
        exact ⟨(γ : G), congrArg Subtype.val hγ⟩) p.2)
    (by
      constructor
      · rintro ⟨c, q⟩ ⟨c', q'⟩ h
        induction q using Quotient.inductionOn' with
        | h y =>
        induction q' using Quotient.inductionOn' with
        | h y' =>
        obtain ⟨g, hg⟩ : ∃ g : G, g • (y' : D) = (y : D) := Quotient.exact' h
        have h1 : g • rep c' = rep c := by
          rw [← show pr (y' : D) = rep c' from y'.2, ← hpr, hg]
          exact y.2
        have hc : c = c' := by
          rw [← hrep c, ← hrep c']
          exact Quotient.sound' ⟨g, h1⟩
        subst hc
        refine congrArg (Sigma.mk c) (Quotient.sound' ⟨⟨g, h1⟩, Subtype.ext hg⟩)
      · intro q
        induction q using Quotient.inductionOn' with
        | h d =>
        obtain ⟨g, hg⟩ : ∃ g : G, g • pr d = rep (Quotient.mk'' (pr d)) := Quotient.exact' (hrep (Quotient.mk'' (pr d)))
        refine ⟨⟨Quotient.mk'' (pr d), Quotient.mk'' ⟨g • d, (hpr g d).trans hg⟩⟩, ?_⟩
        exact Quotient.sound' ⟨g, rfl⟩)

theorem fibre_card_stab (x : D₀) (y : fibre pr hpr x) :
    Nat.card (MulAction.stabilizer (MulAction.stabilizer G x) y) = Nat.card (MulAction.stabilizer G (y : D)) := by
  have h1 : ∀ γ : MulAction.stabilizer (MulAction.stabilizer G x) y,
      ((γ : MulAction.stabilizer G x) : G) ∈ MulAction.stabilizer G (y : D) := fun γ =>
    MulAction.mem_stabilizer_iff.mpr (congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp γ.2))
  have hy : pr (y : D) = x := y.2
  have h2 : ∀ g : MulAction.stabilizer G (y : D), (g : G) ∈ MulAction.stabilizer G x := by
    intro g
    have hg : (g : G) • (y : D) = y := MulAction.mem_stabilizer_iff.mp g.2
    refine MulAction.mem_stabilizer_iff.mpr ?_
    calc (g : G) • x = (g : G) • pr (y : D) := by rw [hy]
      _ = pr ((g : G) • (y : D)) := (hpr _ _).symm
      _ = pr (y : D) := by rw [hg]
      _ = x := hy
  have h3 : ∀ g : MulAction.stabilizer G (y : D),
      (⟨(g : G), h2 g⟩ : MulAction.stabilizer G x) ∈ MulAction.stabilizer (MulAction.stabilizer G x) y := fun g =>
    MulAction.mem_stabilizer_iff.mpr (Subtype.ext (MulAction.mem_stabilizer_iff.mp g.2))
  exact Nat.card_congr ⟨fun γ => ⟨_, h1 γ⟩, fun g => ⟨_, h3 g⟩, fun γ => rfl, fun g => rfl⟩

end Fib

namespace GSD

variable (S : GSD K)

end GSD

namespace BiPair

variable {S S' : GSD K} (P : BiPair S S')

end BiPair

namespace GFam

variable (F : GFam K)

end GFam

namespace GSD

variable (K)

end GSD

end Formalism.L2.Col
