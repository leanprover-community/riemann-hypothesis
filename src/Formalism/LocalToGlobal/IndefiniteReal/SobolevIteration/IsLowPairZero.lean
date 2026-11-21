import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.ParabSt
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FuncSt
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.BaseSt
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Tow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def perpSub (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E) :
    AddSubgroup (Matrix (Fin T.rank) (Fin S.rank) D.host.E) where
  carrier := {x | Formalism.IndefR.Eqv.IsPerpI S T C x}
  zero_mem' := by simp [Formalism.IndefR.Eqv.IsPerpI]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Formalism.IndefR.Eqv.IsPerpI] at ha hb ⊢
    rw [Matrix.mul_add, ha, hb, add_zero]
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, Formalism.IndefR.Eqv.IsPerpI] at ha ⊢
    rw [Matrix.mul_neg, ha, neg_zero]

def uX (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : Matrix (Fin S.rank) (Fin r) D.host.E :=
  S.gram⁻¹ * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x * T.gram * C

def gramX (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : Matrix (Fin r) (Fin r) D.host.E :=
  Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (uX S T C x) * S.gram * uX S T C x

def jX (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (μ : Measure (Mx D r S.rank)) (𝓕L : Set (Mx D r S.rank)) (νN : Measure (NI T C)) (𝓕N : Set (NI T C))
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ)
    (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (h : GA D S) (g : GA D T) : ℂ :=
  ∫ n in 𝓕N, Formalism.IndefR.Eqv.ellI S T C μ 𝓕L (heisO ψ S T (ratW T S x) (om (h, (n : GA D T) * g) f)) ∂νN

def KerExp (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle),
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
      ∀ (μ : Measure (Mx D r S.rank)) (𝓕L : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (Formalism.IndefR.Eqv.ratMx D r S.rank) 𝓕L μ →
      ∀ (νN : Measure (NI T C)) (𝓕N : Set (NI T C)), νN.IsHaarMeasure → IsFundamentalDomain (NIQ T C) 𝓕N νN →
        ∃ κ : ℂ, κ ≠ 0 ∧ ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilDatumO ψ S T χS χT om →
          ∀ (h : GA D S) (g : GA D T) (f : WO S T → ℂ), IsThetaFunO ψ S T f →
            HasSum (fun q : Matrix (Fin T.rank) (Fin S.rank) D.host.E ⧸ perpSub S T C =>
                κ * jX ψ C μ 𝓕L νN 𝓕N om f (Quotient.out q) h g)
              (∫ n in 𝓕N, thetaKO om h ((n : GA D T) * g) f ∂νN)

def JGramNZ (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle),
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
      ∀ (μ : Measure (Mx D r S.rank)) (𝓕L : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (Formalism.IndefR.Eqv.ratMx D r S.rank) 𝓕L μ →
      ∀ (νN : Measure (NI T C)) (𝓕N : Set (NI T C)), νN.IsHaarMeasure → IsFundamentalDomain (NIQ T C) 𝓕N νN →
        ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilDatumO ψ S T χS χT om →
          ∀ (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
            gramX S T C x ≠ 0 → ∀ (h : GA D S) (g : GA D T), jX ψ C μ 𝓕L νN 𝓕N om f x h g = 0

def JNU (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle),
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
      ∀ (μ : Measure (Mx D r S.rank)) (𝓕L : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (Formalism.IndefR.Eqv.ratMx D r S.rank) 𝓕L μ →
      ∀ (νN : Measure (NI T C)) (𝓕N : Set (NI T C)), νN.IsHaarMeasure → IsFundamentalDomain (NIQ T C) 𝓕N νN →
        ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilDatumO ψ S T χS χT om →
          ∀ (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
            gramX S T C x = 0 → ∀ u ∈ NI S (uX S T C x), ∀ (h : GA D S) (g : GA D T),
              jX ψ C μ 𝓕L νN 𝓕N om f x (u * h) g = jX ψ C μ 𝓕L νN 𝓕N om f x h g

def CuspUnfold : Prop :=
  ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (Γ : Subgroup H) [DiscreteTopology Γ] (𝓕 : Set H),
    IsFundamentalDomain Γ 𝓕 ν →
    ∀ (X : Type) [MulAction Γ X] [Countable X] (N : X → Subgroup H),
      (∀ x, IsClosed (N x : Set H)) →
      (∀ (γ : Γ) x, N (γ • x) = (N x).map (MulAut.conj (γ : H)).toMonoidHom) →
      (∀ x, ∃ K : Set H, IsCompact K ∧ ∀ u ∈ N x, ∃ γ ∈ Γ, γ ∈ N x ∧ γ * u ∈ K) →
      (∀ (γ : Γ) x, (γ : H) ∈ N x → γ • x = x) →
      ∀ F : H → ℂ, Continuous F → (∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) →
      (∀ x (μx : Measure (N x)) (𝓕x : Set (N x)), μx.IsHaarMeasure →
        IsFundamentalDomain (Γ.subgroupOf (N x)) 𝓕x μx → ∀ h, ∫ u in 𝓕x, F ((u : H) * h) ∂μx = 0) →
      ∀ φ : X → H → ℂ, (∀ x, Measurable (φ x)) → (∀ (γ : Γ) x h, φ (γ • x) h = φ x ((γ : H)⁻¹ * h)) →
        (∀ x, ∀ u ∈ N x, ∀ h, φ x (u * h) = φ x h) → (∀ h, Summable fun x => ‖φ x h‖) →
        Integrable (fun h => ∑' x, ‖φ x h‖ * ‖F h‖) (ν.restrict 𝓕) →
        ∫ h in 𝓕, ∑' x, φ x h * F h ∂ν = 0

def CtFull (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle),
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
      ∀ (μ : Measure (Mx D r S.rank)) (𝓕L : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (Formalism.IndefR.Eqv.ratMx D r S.rank) 𝓕L μ →
      ∀ (νN : Measure (NI T C)) (𝓕N : Set (NI T C)), νN.IsHaarMeasure → IsFundamentalDomain (NIQ T C) 𝓕N νN →
        SFinite (νN.restrict 𝓕N) →
        ∃ κ : ℂ, κ ≠ 0 ∧ ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilDatumO ψ S T χS χT om →
          ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν →
            SFinite (ν.restrict 𝓕) →
            ∀ F : GA D S → ℂ, IsAutFun S F → IsCuspFun S F →
              ∀ (g : GA D T) (f : WO S T → ℂ), IsThetaFunO ψ S T f →
                Integrable (fun p : NI T C × GA D S => thetaKO om p.2 ((p.1 : GA D T) * g) f * F p.2)
                  ((νN.restrict 𝓕N).prod (ν.restrict 𝓕)) →
                Integrable (fun h => ∑' q : Matrix (Fin T.rank) (Fin S.rank) D.host.E ⧸ perpSub S T C,
                    ‖jX ψ C μ 𝓕L νN 𝓕N om f (Quotient.out q) h g‖ * ‖F h‖) (ν.restrict 𝓕) →
                (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
                  Measurable fun h => jX ψ C μ 𝓕L νN 𝓕N om f x h g) →
                ∫ n in 𝓕N, Formalism.IndefR.Lift.liftInt ν 𝓕
                    (fun (g' : GA D T) (h : GA D S) (s : WO S T → ℂ) => thetaKO om h g' s) f F ((n : GA D T) * g) ∂νN =
                  κ * ∫ h in 𝓕, Formalism.IndefR.Eqv.ellI S T C μ 𝓕L (om (h, g) f) * F h ∂ν

def CtFullOf (D : D7) : Prop :=
  Formalism.IndefR.Eqv.ParabN D → KerExp D → JGramNZ D → JNU D → CuspUnfold → Formalism.IndefR.Eqv.GATop D →
    Formalism.IndefR.Eqv.GQDiscrete D → (∀ V : HSp D, ∀ ν : Measure (GA D V), ν.IsHaarMeasure → ν.IsMulRightInvariant) →
    (∀ (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
      ∃ K : Set (NI V C), IsCompact K ∧ ∀ n : NI V C, ∃ γ ∈ NIQ V C, γ * n ∈ K) → CtFull D

end Formalism.IndefR.Tow

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Tow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def liftO {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ν : Measure (GA D S))
    (𝓕 : Set (GA D S)) (f : WO S T → ℂ) (F : GA D S → ℂ) : GA D T → ℂ :=
  Formalism.IndefR.Lift.liftInt ν 𝓕 (fun (g' : GA D T) (h : GA D S) (s : WO S T → ℂ) => thetaKO om h g' s) f F

def CtInteg (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (μ : Measure (Mx D r S.rank)) (𝓕L : Set (Mx D r S.rank)) (νN : Measure (NI T C)) (𝓕N : Set (NI T C))
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ν : Measure (GA D S)) (𝓕 : Set (GA D S))
    (F : GA D S → ℂ) (g : GA D T) (f : WO S T → ℂ) : Prop :=
  Integrable (fun p : NI T C × GA D S => thetaKO om p.2 ((p.1 : GA D T) * g) f * F p.2)
      ((νN.restrict 𝓕N).prod (ν.restrict 𝓕)) ∧
    Integrable (fun h => ∑' q : Matrix (Fin T.rank) (Fin S.rank) D.host.E ⧸ perpSub S T C,
      ‖jX ψ C μ 𝓕L νN 𝓕N om f (Quotient.out q) h g‖ * ‖F h‖) (ν.restrict 𝓕) ∧
    ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, Measurable fun h => jX ψ C μ 𝓕L νN 𝓕N om f x h g

def ConstTermLow (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T T' : HSp D) (χS χT : (AE D)ˣ →* Circle),
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (r : ℕ) (C C' : Matrix (Fin T.rank) (Fin r) D.host.E) (B : Matrix (Fin T.rank) (Fin T'.rank) D.host.E),
      Formalism.IndefR.Mi.IsQuotFrame T C C' T' B →
      ∀ (μ : Measure (Mx D r S.rank)) (𝓕L : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (Formalism.IndefR.Eqv.ratMx D r S.rank) 𝓕L μ →
      ∀ (νN : Measure (NI T C)) (𝓕N : Set (NI T C)), νN.IsHaarMeasure → IsFundamentalDomain (NIQ T C) 𝓕N νN →
        SFinite (νN.restrict 𝓕N) →
        ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
          (om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)),
          IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T' χS χT om' →
          Formalism.IndefR.Mi.IsDescOf ψ S T C C' T' B μ 𝓕L om om' →
          ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν →
            SFinite (ν.restrict 𝓕) →
            ∀ F : GA D S → ℂ, IsAutFun S F → IsCuspFun S F →
              ∀ (g : GA D T) (f : WO S T → ℂ), IsThetaFunO ψ S T f →
                CtInteg ψ C μ 𝓕L νN 𝓕N om ν 𝓕 F g f →
                ∫ n in 𝓕N, liftO om ν 𝓕 f F ((n : GA D T) * g) ∂νN =
                  κ * liftO om' ν 𝓕 (Formalism.IndefR.Mi.desc ψ S T C μ 𝓕L T' B (om (1, g) f)) F 1

def CuspOfLowVanish (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle),
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilDatumO ψ S T χS χT om →
    ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν →
      SFinite (ν.restrict 𝓕) →
      ∀ F : GA D S → ℂ, IsAutFun S F → IsCuspFun S F → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
        (∀ (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
          ∃ (T' : HSp D) (C' : Matrix (Fin T.rank) (Fin r) D.host.E) (B : Matrix (Fin T.rank) (Fin T'.rank) D.host.E),
            Formalism.IndefR.Mi.IsQuotFrame T C C' T' B) →
        (∀ (T' : HSp D) (r : ℕ) (C C' : Matrix (Fin T.rank) (Fin r) D.host.E)
          (B : Matrix (Fin T.rank) (Fin T'.rank) D.host.E), Formalism.IndefR.Mi.IsQuotFrame T C C' T' B →
          ∀ om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ), IsWeilDatumO ψ S T' χS χT om' →
            ∀ f' : WO S T' → ℂ, IsThetaFunO ψ S T' f' → liftO om' ν 𝓕 f' F 1 = 0) →
        (∀ (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
          ∀ (νN : Measure (NI T C)) (𝓕N : Set (NI T C)), νN.IsHaarMeasure → IsFundamentalDomain (NIQ T C) 𝓕N νN →
            ∃ (μ : Measure (Mx D r S.rank)) (𝓕L : Set (Mx D r S.rank)), μ.IsAddHaarMeasure ∧
              IsAddFundamentalDomain (Formalism.IndefR.Eqv.ratMx D r S.rank) 𝓕L μ ∧
              ∀ g : GA D T, CtInteg ψ C μ 𝓕L νN 𝓕N om ν 𝓕 F g f) →
        IsCuspFun T (liftO om ν 𝓕 f F)

end Formalism.IndefR.Tow

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory IsDedekindDomain NumberField

namespace Formalism.IndefR.Tow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open Classical in

def IsLowPair (θ : InfFam D) {S T' : HSp D} {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss)
    (om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)) (pt' : MvPolynomial (FVar D T'.rank S.rank) ℂ → (WO S T' → ℂ))
    (B : MvPolynomial (FVar D T'.rank S.rank) ℂ → M.Vec → (GA D T' → ℂ)) : Prop :=
  (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D S τ), ∀ φ φ', pt' φ' = om' (atTau θ S τ g, 1) (pt' φ) →
    ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → B φ' (Function.update v τ w) = B φ v) ∧
  (∀ τ, ∀ X ∈ lieAt S τ, ∀ φ φ', (∀ z, HasDerivAt (fun t : ℝ => om' (oneP θ S τ X t, 1) (pt' φ) z) (pt' φ' z) 0) →
    ∀ (v : M.Vec) (w : M.sm τ),
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v τ)) (w : M.H τ) 0 →
      B φ' v + B φ (Function.update v τ w) = 0) ∧
  (∀ τ, ∀ k ∈ Formalism.QuantumDeterminants.UH (gramAt D T' τ), ∀ φ φ', pt' φ' = om' (1, atTau θ T' τ k) (pt' φ) →
    ∀ v g', B φ' v g' = B φ v (g' * atTau θ T' τ k)) ∧
  (∀ τ, ∀ Y ∈ lieAt T' τ, ∀ φ φ', (∀ z, HasDerivAt (fun t : ℝ => om' (1, oneP θ T' τ Y t) (pt' φ) z) (pt' φ' z) 0) →
    ∀ v g', HasDerivAt (fun t : ℝ => B φ v (g' * oneP θ T' τ Y t)) (B φ' v g') 0)

def liftPair {S T' : HSp D} {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss)
    (om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)) (pt' : MvPolynomial (FVar D T'.rank S.rank) ℂ → (WO S T' → ℂ))
    (ν : Measure (GA D S)) (𝓕 : Set (GA D S)) (T : MMap M) : MvPolynomial (FVar D T'.rank S.rank) ℂ → M.Vec → (GA D T' → ℂ) :=
  fun φ v => liftO om' ν 𝓕 (pt' φ) (T v)

def LowDom (θ : InfFam D) {S T' : HSp D} {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss)
    (om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)) (pt' : MvPolynomial (FVar D T'.rank S.rank) ℂ → (WO S T' → ℂ))
    (ν : Measure (GA D S)) (𝓕 : Set (GA D S)) (T : MMap M) : Prop :=
  (∀ τ, ∀ X ∈ lieAt S τ, ∀ φ (v : M.Vec) (g' : GA D T'),
    (∀ t : ℝ, |t| < 1 → IntegrableOn (fun h => thetaKO om' (h * oneP θ S τ X t) g' (pt' φ) *
      T v (h * oneP θ S τ X t)) 𝓕 ν) ∧
    ∃ G : GA D S → ℝ, IntegrableOn G 𝓕 ν ∧ ∀ t : ℝ, |t| < 1 → ∀ h ∈ 𝓕,
      ‖deriv (fun s : ℝ => thetaKO om' (h * oneP θ S τ X s) g' (pt' φ) * T v (h * oneP θ S τ X s)) t‖ ≤ G h) ∧
  (∀ τ, ∀ Y ∈ lieAt T' τ, ∀ φ (v : M.Vec) (g' : GA D T'),
    (∀ t : ℝ, |t| < 1 → IntegrableOn (fun h => thetaKO om' h (g' * oneP θ T' τ Y t) (pt' φ) * T v h) 𝓕 ν) ∧
    ∃ G : GA D S → ℝ, IntegrableOn G 𝓕 ν ∧ ∀ t : ℝ, |t| < 1 → ∀ h ∈ 𝓕,
      ‖deriv (fun s : ℝ => thetaKO om' h (g' * oneP θ T' τ Y s) (pt' φ) * T v h) t‖ ≤ G h)

def LowKerDer (θ : InfFam D) {S T' : HSp D} (om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ))
    (pt' : MvPolynomial (FVar D T'.rank S.rank) ℂ → (WO S T' → ℂ)) : Prop :=
  (∀ τ, ∀ X ∈ lieAt S τ, ∀ φ φ', (∀ z, HasDerivAt (fun t : ℝ => om' (oneP θ S τ X t, 1) (pt' φ) z) (pt' φ' z) 0) →
    ∀ h g', HasDerivAt (fun t : ℝ => thetaKO om' (h * oneP θ S τ X t) g' (pt' φ)) (thetaKO om' h g' (pt' φ')) 0) ∧
  (∀ τ, ∀ Y ∈ lieAt T' τ, ∀ φ φ', (∀ z, HasDerivAt (fun t : ℝ => om' (1, oneP θ T' τ Y t) (pt' φ) z) (pt' φ' z) 0) →
    ∀ h g', HasDerivAt (fun t : ℝ => thetaKO om' h (g' * oneP θ T' τ Y t) (pt' φ)) (thetaKO om' h g' (pt' φ')) 0)

def LowPairOfLift (D : D7) : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T' : HSp D) (χS χT : (AE D)ˣ →* Circle)
    {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss) (J : Set (GA D S)) (χ : GA D S → ℂ) (T : MMap M),
    IsMultMap θ M J χ T →
    ∀ om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ), IsWeilDatumO ψ S T' χS χT om' →
    ∀ pt' : MvPolynomial (FVar D T'.rank S.rank) ℂ → (WO S T' → ℂ), (∀ φ, IsThetaFunO ψ S T' (pt' φ)) →
    ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), MeasurableSet 𝓕 →
      (∀ Φ : GA D S → ℂ, (∀ γ ∈ GQ S, ∀ h, Φ (γ * h) = Φ h) → ∀ k : GA D S,
        (IntegrableOn (fun h => Φ (h * k)) 𝓕 ν ↔ IntegrableOn Φ 𝓕 ν) ∧ ∫ h in 𝓕, Φ (h * k) ∂ν = ∫ h in 𝓕, Φ h ∂ν) →
      LowKerDer θ om' pt' → LowDom θ M om' pt' ν 𝓕 T →
      IsLowPair θ M om' pt' (liftPair M om' pt' ν 𝓕 T)

end Formalism.IndefR.Tow

end
end
