import Formalism.LocalToGlobal.UnitaryNorms.CharExGen
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

namespace CharEx

section Sub

variable {L : Type} [Field L] [NumberField L] (F : Type) [Field F] [NumberField F] [Algebra F L]

def aF (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : Ideles L :=
  ∏ P ∈ aboveF (L := L) F v, localIdele L P (atFin P (upF F k))

def aFi (w : InfinitePlace F) (k : Fˣ) : Ideles L :=
  ∏ w' ∈ aboveInf (L := L) F w, infIdele L w' (atInf w' (upF F k))

def idF : Subgroup (Ideles L) :=
  Subgroup.closure (Set.range (fun p : HeightOneSpectrum (𝓞 F) × Fˣ => (aF F p.1 p.2 : Ideles L)) ∪
    Set.range (fun p : InfinitePlace F × Fˣ => (aFi F p.1 p.2 : Ideles L)))

def unitF : Subgroup (Ideles L) := unitIdeles L ⊔ idF (L := L) F



theorem resFin_eq (χ : HChar L) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : χ.resFin v k = χ.1 (aF F v k) := by
  unfold HChar.resFin aF
  rw [map_prod, MonoidHom.finset_prod_apply]
  exact Finset.prod_congr rfl fun P _ => rfl

theorem resInf_eq (χ : HChar L) (w : InfinitePlace F) (k : Fˣ) : χ.resInf w k = χ.1 (aFi F w k) := by
  unfold HChar.resInf aFi
  rw [map_prod, MonoidHom.finset_prod_apply]
  exact Finset.prod_congr rfl fun w' _ => rfl

end Sub

section Loc

variable {L : Type} [Field L] [NumberField L]



end Loc

variable {R : Formalism.BasicNotions.Ranks} {H : Formalism.BasicNotions.Host R}

structure EtaTQ (Φ : Ideles H.E →* ℂˣ) : Prop where
  cont : Continuous Φ
  unitU : ∀ u ∈ unitIdeles H.E, ‖((Φ u : ℂˣ) : ℂ)‖ = 1
  unr : ∀ v x, IsUnitAt v x → Φ (localIdele H.E v x) = 1
  resFin : ∀ v k, Φ (aF H.F v k) = etaFin (L := H.E) H.F v k
  resInf : ∀ w k, Φ (aFi H.F w k) = etaInf H.F w k
  inf : ∀ k : H.Eˣ, ((Φ (infDiag k) : ℂˣ) : ℂ) =
    ∏ τ ∈ @Finset.univ R.Psi (Fintype.ofFinite _), (embPsi H τ (k : H.E) / ((‖embPsi H τ (k : H.E)‖ : ℝ) : ℂ)) ^ (1 : ℤ)
  glob : ∀ k : H.Eˣ, diagUnits H.E k ∈ unitF (L := H.E) H.F → Φ (diagUnits H.E k) = 1

structure Mu0Q (P : PiBar H) (W : Omg H) (e : R.Psi → ℚ) (j : ℕ) (Φ : Ideles H.E →* ℂˣ) : Prop where
  cont : Continuous Φ
  unitU : ∀ u ∈ unitIdeles H.E, ‖((Φ u : ℂˣ) : ℂ)‖ = 1
  trivFin : ∀ v k, Φ (aF H.F v k) = 1
  trivInf : ∀ w k, Φ (aFi H.F w k) = 1
  inf : ∃ n : R.Psi → ℤ, (∀ τ, (n τ : ℚ) = 2 * (-e τ)) ∧ ∀ k : H.Eˣ, ((Φ (infDiag k) : ℂˣ) : ℂ) =
    ∏ τ ∈ @Finset.univ R.Psi (Fintype.ofFinite _), (embPsi H τ (k : H.E) / ((‖embPsi H τ (k : H.E)‖ : ℝ) : ℂ)) ^ n τ
  unr : ∀ v, (∀ k, ¬ OverP H (H.g k) v) → ∀ x, IsUnitAt v x → Φ (localIdele H.E v x) = 1
  tame : ∀ v x, IsUnitAt v x → Valued.v ((x : v.adicCompletion H.E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) →
    Φ (localIdele H.E v x) = 1
  atg : ∀ (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)), P.Div k w → ∀ (a : ℕ) (ha : a.Coprime (H.g k)) (x : H.Eˣ),
    (x : H.E) = (a : H.E) → Φ (localIdele H.E w (atFin w x)) = (W.om k (ZMod.unitOfCoprime a ha) ^ (2 * (j + 1)))⁻¹
  glob : ∀ k : H.Eˣ, diagUnits H.E k ∈ unitF (L := H.E) H.F → Φ (diagUnits H.E k) = 1

structure DeltaQ (p : ℕ) (Φ : Ideles H.E →* ℂˣ) : Prop where
  cont : Continuous Φ
  finU : ∃ n : ℕ, 0 < n ∧ ∀ u ∈ unitIdeles H.E, Φ u ^ n = 1
  trivFin : ∀ v k, Φ (aF H.F v k) = 1
  trivInf : ∀ w k, Φ (aFi H.F w k) = 1
  tame : ∀ v x, IsUnitAt v x → Valued.v ((x : v.adicCompletion H.E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) →
    Φ (localIdele H.E v x) = 1
  unr : ∀ v, ¬ OverP H p v → ∀ x, IsUnitAt v x → Φ (localIdele H.E v x) = 1
  ine : ∀ v, OverP H p v → ∀ n : ℕ, (∀ x, IsUnitAt v x → Φ (localIdele H.E v x) ^ n = 1) ↔ 15 ∣ n
  glob : ∀ k : H.Eˣ, diagUnits H.E k ∈ unitF (L := H.E) H.F → Φ (diagUnits H.E k) = 1





end CharEx

end Formalism.L2.Host
