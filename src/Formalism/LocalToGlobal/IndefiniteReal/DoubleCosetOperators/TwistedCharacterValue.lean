import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.ImaginaryGeneratorMulDenominator
import Formalism.LocalToGlobal.Columns.MemWmPerp
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.NX Formalism.L2.Col
open scoped TensorProduct

namespace Formalism.IndefR.NX

section PsiU


end PsiU

section BC

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] {G : Type} [Group G]

def bcRep {W₀ : Type} [AddCommGroup W₀] [Module K W₀] (ρ₀ : Representation K G W₀) :
    Representation K' G (K' ⊗[K] W₀) where
  toFun γ := (ρ₀ γ).baseChange K'
  map_one' := by rw [map_one]; exact LinearMap.baseChange_id
  map_mul' γ δ := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

theorem toMatrix_bcRep {W₀ : Type} [AddCommGroup W₀] [Module K W₀] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W₀) (ρ₀ : Representation K G W₀) (γ : G) :
    LinearMap.toMatrix (Algebra.TensorProduct.basis K' b) (Algebra.TensorProduct.basis K' b) (bcRep (K' := K') ρ₀ γ) =
      (LinearMap.toMatrix b b (ρ₀ γ)).map (algebraMap K K') :=
  LinearMap.toMatrix_baseChange K' (ρ₀ γ) b b

end BC

section AdlK

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

end AdlK

section AlgBC

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K K' : Type} [Field K] [Field K'] [Algebra K K']

theorem isAlgWeightF_bc {W₀ : Type} [AddCommGroup W₀] [Module K W₀]
    (ρ₀ : Representation K (GQ L n) W₀) (h : IsAlgWeightF L n K ρ₀) : IsAlgWeightF L n K' (bcRep (K' := K') ρ₀) := by
  obtain ⟨hfd, ι, hι, hdec, bs, κ, hκ, eb, P, hP⟩ := h
  have := hfd
  refine ⟨inferInstance, ι, hι, hdec, Algebra.TensorProduct.basis K' bs, κ, hκ, eb,
    fun a a' => MvPolynomial.map (algebraMap K K') (P a a'), fun γ γ₀ hγ => ?_⟩
  rw [toMatrix_bcRep, hP γ γ₀ hγ]
  ext a a'
  simp only [MvPolynomial.eval_map]
  show algebraMap K K' (MvPolynomial.eval₂ (RingHom.id K) _ (P a a')) = _
  rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  congr 1
  funext p
  simp [map_ratCast]

end AlgBC

section Real

variable (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
  (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ)
  (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)

abbrev algKk : Algebra (FractionRing (D.ntw.O i)) (Kk D i k) := (toKk D i k).toAlgebra

attribute [local instance] algKk

def BCIrr {W₀ : Type} [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀) : Prop :=
  (bcRep (K' := Kk D i k) ρ₀).IsIrreducible

end Real

section LevGen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

end LevGen

section LevNX

variable (D : D7) (i : D.ntw.Tw) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
  (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ)
  (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
  (sp : PlE D.host → SplitPlace D.host.E) (QP DP : Finset (PlE D.host))

abbrev sgNX : (Σ kk : Fin 2, D.nd.PlG kk) → SplitPlace D.host.E := fun kv => sp (pG D kv)

abbrev sqNX : {P // P ∈ QP} ⊕ {P // P ∈ DP} → SplitPlace D.host.E :=
  Sum.elim (fun P : {P // P ∈ QP} => sp P.1) (fun P : {P // P ∈ DP} => sp P.1)

end LevNX

section ChrG


theorem supSum_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {r : ℕ} (A : Matrix (Fin r) (Fin r) R) :
    Formalism.L2.NX.supSum r (A.map f) = f (Formalism.L2.NX.supSum r A) := by
  unfold Formalism.L2.NX.supSum
  simp only [map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

section RedGen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => NumberField.maximalRealSubfield L

variable {F : Type} [CommRing F]

theorem intLift_of_mem (v : HeightOneSpectrum (𝓞 L⁺)) (y : v.adicCompletion L⁺)
    (h : y ∈ v.adicCompletionIntegers L⁺) : intLift v y = ⟨y, h⟩ := by
  unfold intLift
  rw [dif_pos h]



end RedGen

variable (D : D7) (i : D.ntw.Tw) (b : Bool) (k : ℕ)
  (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
  (sp : PlE D.host → SplitPlace D.host.E)

open Classical in

theorem psiUTot_single (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (FractionRing (D.ntw.O i))ˣ)
    (hU : D.nexp.U = U D.nd)
    (hψ : ∀ (u : D.nexp.U), D.nexp.psiU i b u = psiUD D i θ b ⟨u.1, by rw [← hU]; exact u.2⟩)
    (kv : Σ kk : Fin 2, D.nd.PlG kk) (Gm : GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
    (hG : IsUniTri D.R.r (Gm : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) :
    psiUTot D i b (Pi.mulSingle kv Gm) = ((thSide D.host.g θ b kv.1 (Multiplicative.ofAdd (xiRed D kv *
      Formalism.L2.NX.supSum D.R.r (Gm : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))) :
        (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) := by
  classical
  have hmem : (Pi.mulSingle kv Gm : G0g D.nd) ∈ D.nexp.U := by
    rw [hU, mem_U]
    intro kv'
    by_cases h : kv' = kv
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact ⟨fun a c hca => hG.1 hca, hG.2⟩
    · rw [Pi.mulSingle_eq_of_ne h]
      refine ⟨fun a c hca => ?_, fun a => by simp⟩
      have hne : a ≠ c := fun e => by subst e; exact lt_irrefl _ hca
      simp [Matrix.one_apply_ne hne]
  unfold psiUTot
  rw [dif_pos hmem, hψ ⟨_, hmem⟩, psiUD, psiUOf_apply, Finset.prod_eq_single kv]
  · dsimp only
    rw [Pi.mulSingle_eq_same]
  · intro kv' _ hne
    dsimp only
    rw [Pi.mulSingle_eq_of_ne hne]
    simp [Formalism.L2.NX.supSum_one]
  · intro h
    exact absurd (Finset.mem_univ kv) h

open Classical in

theorem gVal_of (kv : Σ kk : Fin 2, D.nd.PlG kk) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ' : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (xm : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E)))
    (G : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) (hrn : D.R.r ≤ D.R.nV)
    (hG : redMat s.v red (topR hrn xm) = G)
    (u : (ZMod (D.host.g kv.1))ˣ) (hu : red (intLift s.v (detT D.R.r xm)) = (u : ZMod (D.host.g kv.1))) :
    gVal D i k b kv s red τ' xm = toKk D i k (psiUTot D i b (Pi.mulSingle kv (glOf G))) *
      toKk D i k ((τ' u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) := by
  have hU' : IsUnit (red (intLift s.v (detT D.R.r xm))) := by rw [hu]; exact u.isUnit
  unfold gVal
  show toKk D i k (psiUTot D i b (Pi.mulSingle kv (glOf (redMat s.v red (topR hrn xm))))) *
    (if h : IsUnit (red (intLift s.v (detT D.R.r xm))) then
      toKk D i k ((τ' h.unit : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) else 1) = _
  rw [hG, dif_pos hU', show hU'.unit = u from Units.ext (by rw [IsUnit.unit_spec, hu])]

end ChrG

section Tau

variable (D : D7)

def TauTame (i : D.ntw.Tw) (j : ℕ) (b : Bool) (kv : Σ kk : Fin 2, D.nd.PlG kk) : Prop :=
  ∃ τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ, ∀ (x : (ZMod (D.host.g kv.1))ˣ) (u : 𝓞 D.host.E),
    (((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - u) ∈ (pG D kv).asIdeal →
    ((τ x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      ringHomOfBaseOrderToFraction D i (tameVal (D.ntw.chi1 i j b) (pG D kv) 1 u).1

open Classical in

def tauNX (i : D.ntw.Tw) (j : ℕ) (b : Bool) (kv : Σ kk : Fin 2, D.nd.PlG kk) :
    (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ :=
  if h : TauTame D i j b kv then h.choose else 1


end Tau

section Assembly

variable (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
  (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ)
  (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)

attribute [local instance] algKk

end Assembly

section Pq

variable (D : D7)

open Classical in

def qpOf (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : Finset (PlE D.host)) :
    Finset (PlE D.host) :=
  S.filter fun P => ∀ v, NG.OverPl P v → P = Pq v ∨ Pq v ∉ S

theorem qpOf_sub (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : Finset (PlE D.host)) :
    qpOf D Pq S ⊆ S := by
  classical
  intro P hP
  unfold qpOf at hP
  exact (Finset.mem_filter.1 hP).1

theorem qpOf_eq (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : Finset (PlE D.host))
    {P : PlE D.host} (hP : P ∈ qpOf D Pq S) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))}
    (hv : NG.OverPl P v) (hS : Pq v ∈ S) : P = Pq v := by
  classical
  unfold qpOf at hP
  exact ((Finset.mem_filter.1 hP).2 v hv).resolve_right (not_not.2 hS)

end Pq

end Formalism.IndefR.NX
