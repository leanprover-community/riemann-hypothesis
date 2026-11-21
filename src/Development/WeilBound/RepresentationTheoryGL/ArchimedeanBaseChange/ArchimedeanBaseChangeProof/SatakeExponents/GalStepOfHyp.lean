import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.BaseChangeIsobaricOf
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Clause3Asc
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F

structure Pre (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) where
  c : ℕ
  N : Fin c → ℕ
  h : ∑ i, N i = n
  V : ∀ i, Submodule ℂ (Sm E (N i))
  σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E))
  m : Fin c → (E →+* ℂ) → Multiset ℂ
  pos : ∀ i, 0 < N i
  discrete : ∀ i, IsDiscrete (V i)
  loc : ∀ i w, IsLocCompGL (V i) w (σ i w)
  inf : ∀ i τ, HasInfCharGL (V i) τ (m i τ)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def pre (D : Datum E n) : Pre E n := ⟨D.c, D.N, D.h, D.V, D.σ, D.m, D.pos, D.discrete, D.loc, D.inf⟩

def Pre.toDatum (D : Pre E n) (h : ∀ i, IsCsdGL (D.V i)) : Datum E n :=
  ⟨D.c, D.N, D.h, D.V, D.σ, D.m, D.pos, D.discrete, h, D.loc, D.inf⟩

def Pre.Sat (D : Pre E n) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  ∃ b : Fin D.c → Multiset ℂˣ, (∀ i, GlobalTheory.LGrp.IsSpherical (D.σ i w).ρ (GlobalTheory.LFun.KGL w (D.N i)) ∧
    GlobalTheory.LFun.HasSatGL w (D.σ i w).ρ (b i)) ∧ ∑ i, b i = B

def Pre.Reg (D : Pre E n) : Prop := ∀ τ, ∃ lam : DomWeight n, ∑ i, D.m i τ = infOfWeight lam

def ConjPl (w u : HeightOneSpectrum (𝓞 E)) : Prop :=
  u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) ∧ (u ≠ w ∨ ¬ IsSplitAt w)

def Pre.ThetaStable (D : Pre E n) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, D.Sat w B ∧ ∀ u, ConjPl w u → D.Sat u (B.map (·⁻¹))

def Pre.cls (D : Pre E n) (i : Fin D.c) (w : HeightOneSpectrum (𝓞 E)) : GlobalTheory.LocGL.IrrGL (w.adicCompletion E) :=
  GlobalTheory.LocGL.IrrGL.of (D.σ i w).ρ (D.σ i w).smooth (D.σ i w).irred

def WeightEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)),
  IsAutRepU π → ∀ τ, ∃ lam, HasWeightAt π τ lam

def Strings : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Pre E n), D.Reg → ∀ i,
  ∃ (a d : ℕ) (P : CuspSub E a), 1 ≤ a ∧ 1 ≤ d ∧ P.IsUnitary ∧ IsNormalised P ∧ ∀ P', P.Iso P' → AscEmb (D.V i) P' d

def CuspCsd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Pre E n), D.Reg → D.ThetaStable →
  ∀ i (a d : ℕ) (P : CuspSub E a), 1 ≤ a → 1 ≤ d → P.IsUnitary → IsNormalised P → AscEmb (D.V i) P d → P.IsCsd

def RegAlg {N : ℕ} (n : ℕ) (V : Submodule ℂ (Sm E N)) : Prop :=
  ∀ τ, ∃ m, HasInfCharGL V τ m ∧ m.Nodup ∧ ∀ x ∈ m, ∃ k : ℤ, x = k + ((n : ℂ) - 1) / 2

def RegPart : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Pre E n), D.Reg → ∀ i,
  RegAlg n (D.V i)

def AscIso : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N a d : ℕ) (V V' : Submodule ℂ (Sm E N))
  (P : CuspSub E a), 1 ≤ N → IsDiscrete V → IsDiscrete V' → RegAlg n V → P.IsUnitary → IsNormalised P → P.IsCsd →
  AscEmb V P d → AscEmb V' P d →
  ∃ T : V ≃ₗ[ℂ] V', ∀ (o : Op E N) (φ ψ : V), ψ.1 = act o φ.1 → (T ψ).1 = act o (T φ).1

def ThetaAsc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N a d : ℕ) (V : Submodule ℂ (Sm E N))
  (P : CuspSub E a), 1 ≤ N → IsDiscrete V → RegAlg n V → P.IsUnitary → IsNormalised P → P.IsCsd → AscEmb V P d →
  ∃ V' : Submodule ℂ (Sm E N), IsDiscrete V' ∧ AscEmb V' P d ∧
    ∃ T : V ≃ₗ[ℂ] V', ∀ (o : Op E N) (φ ψ : V), ψ.1 = act (thetaOp o) φ.1 → (T ψ).1 = act o (T φ).1

def StringCsd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N a d : ℕ) (V : Submodule ℂ (Sm E N))
  (P : CuspSub E a), 1 ≤ N → IsDiscrete V → RegAlg n V → P.IsUnitary → IsNormalised P → AscEmb V P d → P.IsCsd →
  IsCsdGL V



def ThetaOfCsd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Datum E n), (pre D).ThetaStable

def SplitSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)),
  IsAutRepU π → ∀ D D' : Datum E n, Weak π D → Weak π D' →
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ B, (pre D).Sat w B ∧ (pre D').Sat w B

def GalStep : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D D' : Pre E n), D.Reg → D'.Reg →
  D.ThetaStable → D'.ThetaStable →
  (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ D'.Sat w B) →
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, D.Sat w B ∧ D'.Sat w B

def GalStepOfHyp : Prop := GlobalTheory.Published.GaloisRepOfPolarizedPair → GalStep

def LocRigid : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D D' : Pre E n), D.Reg → D'.Reg →
  (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, D.Sat w B ∧ D'.Sat w B) →
  ∃ e : Fin D.c ≃ Fin D'.c, ∀ i w, D.cls i w = D'.cls (e i) w

def PermSub : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D D' : Pre E n)
  (e : Fin D.c ≃ Fin D'.c) (w : HeightOneSpectrum (𝓞 E)), (∀ i, D.cls i w = D'.cls (e i) w) →
  ∀ P : SmIrr (GL (Fin n) (w.adicCompletion E)), GlobalTheory.SmGL.IsSubquotient P.ρ (locProd D'.h w (D'.σ · w)) →
    GlobalTheory.SmGL.IsSubquotient P.ρ (locProd D.h w (D.σ · w))

def PermSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D D' : Pre E n)
  (e : Fin D.c ≃ Fin D'.c) (w : HeightOneSpectrum (𝓞 E)), (∀ i, D.cls i w = D'.cls (e i) w) → ∀ B, D.Sat w B → D'.Sat w B

theorem rigid_of (hW : WeightEx) (hT : ThetaOfCsd) (hS : SplitSat) (hG : GalStep) (hL : LocRigid) (hP : PermSub)
    (hQ : PermSat) : Rigid := by
  intro E _ _ _ n _ π hπ D D' hD hD' w
  have r : ∀ X : Datum E n, Weak π X → (pre X).Reg := fun X hX τ => (hW E n π hπ τ).imp fun lam h => hX.1 τ lam h
  obtain ⟨e, he⟩ := hL E n (pre D) (pre D') (r D hD) (r D' hD')
    (hG E n _ _ (r D hD) (r D' hD') (hT E n D) (hT E n D') (hS E n π hπ D D' hD hD'))
  refine ⟨hP E n (pre D) (pre D') e w fun i => he i w, fun B hB => ?_⟩
  obtain ⟨b, hb, hs⟩ := hQ E n (pre D) (pre D') e w (fun i => he i w) _ ⟨B, hB, rfl⟩
  exact ⟨b, hb, hs.symm⟩

def Pre.SplitAt (π : Submodule ℂ (UA E n → ℂ)) (D : Pre E n) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ P : SmIrr (GL (Fin n) (w.adicCompletion E)), GlobalTheory.SmGL.IsSubquotient P.ρ (locProd D.h w (D.σ · w)) ∧
    IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ

def Pre.Weak (π : Submodule ℂ (UA E n → ℂ)) (D : Pre E n) : Prop :=
  (∀ τ lam, HasWeightAt π τ lam → ∑ i, D.m i τ = infOfWeight lam) ∧
    {w | IsSplitAt w ∧ ¬ D.SplitAt π w}.Finite ∧ D.ThetaStable

def PreSplit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), S.card ≤ 1 →
    ∃ D : Pre E n, D.Weak π ∧
    (∀ w ∈ S, IsSplitAt w → D.SplitAt π w) ∧ ∀ w, IsUnramU π w → ¬ IsSplitAt w → ∃ B, D.Sat w B

def PreInert : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ w, IsUnramU π w → ¬ IsSplitAt w → ∃ D : Pre E n, D.Weak π ∧
    ∀ B, D.Sat w B → ∀ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
      ∀ α, HasSatAt π w s ϖ q α → B = GlobalTheory.LGrp.bcParam n α




end PositivityTheory.Rg.BcB.F

end
