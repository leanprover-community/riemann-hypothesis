import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InfiniteOfConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSplitTorusSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusInLeviParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToIdeleESymm

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.ResLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def col {n r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) : Matrix (Fin n) (Fin 1) E := X.submatrix id fun _ => 0

def Scales (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (p : GAd σ J)
    (l : (AF F ⊗[F] E)ˣ) : Prop := (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x

def lineGrp (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) : Subgroup (GAd σ J) where
  carrier := {p | ∃ l, Scales σ J x p l}
  one_mem' := ⟨1, by simp [Scales]⟩
  mul_mem' := fun {a b} ⟨l, e⟩ ⟨l', e'⟩ => ⟨l * l', by
    unfold Scales at *
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, e', Matrix.mul_smul, e, smul_smul, Units.val_mul, mul_comm]⟩
  inv_mem' := fun {a} ⟨l, e⟩ => ⟨l⁻¹, by
    unfold Scales at *
    have := congrArg (fun Z => (l⁻¹).1 • ((matHom _ σ J a⁻¹).1 * Z)) e
    simp only [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul,
      Matrix.mul_smul, smul_smul, Units.inv_mul, one_smul] at this
    exact this.symm⟩

structure Data (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) : Prop where
  cm : IsCMExt F E σ
  unr : Algebra.Unramified (𝓞 F) (𝓞 E)
  herm : IsHermND σ J
  witt : IsWittFrame σ J X Y
  adapted : GlobalTheory.EisLine.IsAdapted σ J X Y L a
  iwa : ∀ g, ∃ p l, Scales σ J (col X) p l ∧ ∃ k ∈ levelAll σ J L a, g = p * k
  ht : ∀ p l, Scales σ J (col X) p l → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l

def IsReps (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (T : Set (ratPts σ J)) : Prop :=
  ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l, Scales σ J x (γ * t⁻¹ : ratPts σ J).1 l

structure IsFlow (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (a : ℝ → GAd σ J) : Prop where
  cont : Continuous a
  add : ∀ s t, a (s + t) = a s * a t
  onX : ∀ t, ∃ l, Scales σ J (col X) (a t) l ∧ (absE F E l : ℝ) = Real.exp t
  onY : ∀ t, ∃ l, Scales σ J (col Y) (a t) l ∧ (absE F E l : ℝ) = Real.exp (-t)
  mem : ∀ t, a t ∈ GlobalTheory.StdPar.levi σ J X Y {0}
  comm : ∀ t, ∀ m ∈ GlobalTheory.StdPar.levi σ J X Y {0}, a t * m = m * a t

example (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) : Scales σ J x 1 1 := by
  simp [Scales]

structure IsHt {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (h : G → ℝ) : Prop where
  pos : ∀ g, 0 < h g
  cont : Continuous h
  one : ∀ k ∈ K, h k = 1
  iw : ∀ g, ∃ k ∈ K, ∀ x, h (g * x) = h g * h (k * x)

example {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) : IsHt K fun _ => 1 :=
  ⟨fun _ => one_pos, continuous_const, fun _ _ => rfl, fun _ => ⟨1, one_mem _, fun _ => (one_mul _).symm⟩⟩

instance countable_inf {G : Type} [Group G] (Γ H : Subgroup G) [Countable Γ] : Countable (Γ ⊓ H : Subgroup G) :=
  (Subgroup.inclusion_injective inf_le_left).countable

structure SemiLat {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (N M Λ : Subgroup G) (ν : Measure N)
    (π : Measure M) (𝓝 : Set N) (𝓜 : Set M) : Prop where
  closedN : IsClosed (N : Set G)
  closedM : IsClosed (M : Set G)
  norm : ∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N
  disj : ∀ g ∈ N, g ∈ M → g = 1
  dec : ∀ γ ∈ Λ, ∃ u ∈ N, ∃ m ∈ M, u ∈ Λ ∧ m ∈ Λ ∧ γ = u * m
  haarN : ν.IsHaarMeasure
  haarM : π.IsHaarMeasure
  domN : IsFundamentalDomain (Λ.subgroupOf N) 𝓝 ν
  domM : IsFundamentalDomain (Λ.subgroupOf M) 𝓜 π
  finN : ν 𝓝 ≠ ⊤
  finM : π 𝓜 ≠ ⊤
  count : Countable Λ := by infer_instance
  topGrp : IsTopologicalGroup G := by infer_instance
  borel : BorelSpace G := by infer_instance

namespace Inhab

open GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (conjUnit)

variable {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E}

theorem exists_data (hc : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) (hJ : IsHermND σ J)
    (hW : IsWittFrame σ J X Y) {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)}
    (hA : GlobalTheory.EisLine.IsAdapted σ J X Y L a) : ∃ h, Data σ J X Y L a h := by
  obtain ⟨h1, h, h2⟩ := GlobalTheory.IwLine.iwasawa_line F E σ hc hu n J hJ r X Y hW _ rfl L a hA
  exact ⟨h, hc, hu, hJ, hW, hA, h1, h2⟩

theorem data_inhabited : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E) (_ : Algebra F E)
    (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (X Y : Matrix (Fin 2) (Fin (0 + 1)) E) (L : Submodule (𝓞 E) (Fin 2 → E))
    (a : GL (Fin 2) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), Data σ J X Y L a h := by
  obtain ⟨F, E, _, _, _, _, _, σ, J, X, Y, L, a, hc, hu, hJ, hW, hA⟩ := GlobalTheory.EisLineModel.data_inhabited
  obtain ⟨h, H⟩ := exists_data hc hu hJ hW hA
  exact ⟨F, E, _, _, _, _, _, σ, J, X, Y, L, a, h, H⟩

theorem exists_isReps (x : Matrix (Fin n) (Fin 1) E) : ∃ T, IsReps σ J x T := GlobalTheory.EisResLineModel.exists_reps x

omit [NumberField E] in

theorem scales_of_diag {C : Matrix (Fin n) (Fin (r + 1)) E} {p : GAd σ J} {l : Fin (r + 1) → (AF F ⊗[F] E)ˣ}
    (h : (matHom _ σ J p).1 * adMat F C = adMat F C * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E))) :
    Scales σ J (ResLine.col C) p (l 0) := by
  ext i j
  have := congrFun (congrFun h i) 0
  rw [mul_diagonal] at this
  simpa [Matrix.mul_apply, ResLine.col, mul_comm] using this





example (H : Subgroup (GAd σ J)) : Countable (ratPts σ J ⊓ H : Subgroup (GAd σ J)) := inferInstance


abbrev Pl : Type := Multiplicative (Fin 2 → ℝ)

scoped instance measurableSpacePl : MeasurableSpace Pl := borel _

scoped instance borelSpacePl : BorelSpace Pl := ⟨rfl⟩

def axis (i : Fin 2) : Subgroup Pl where
  carrier := {g | ∀ j, j ≠ i → g.toAdd j = 0}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun ha hb j hj => by simp [ha j hj, hb j hj]
  inv_mem' := fun ha j hj => by simp [ha j hj]

def intPts : Subgroup Pl where
  carrier := {g | ∀ j, ∃ m : ℤ, g.toAdd j = m}
  one_mem' := fun _ => ⟨0, by simp⟩
  mul_mem' := fun ha hb j => let ⟨m, e⟩ := ha j; let ⟨m', e'⟩ := hb j; ⟨m + m', by simp [e, e']⟩
  inv_mem' := fun ha j => let ⟨m, e⟩ := ha j; ⟨-m, by simp [e]⟩

theorem cont_coord (j : Fin 2) : Continuous fun g : Pl => g.toAdd j := (continuous_apply j).comp continuous_toAdd

theorem isClosed_axis (i : Fin 2) : IsClosed (axis i : Set Pl) := by
  have : (axis i : Set Pl) = ⋂ j, ⋂ (_ : j ≠ i), {g | g.toAdd j = 0} := by ext g; simp [axis]
  rw [this]
  exact isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (cont_coord j) continuous_const

scoped instance locallyCompactSpace_axis (i : Fin 2) : LocallyCompactSpace (axis i) := (isClosed_axis i).locallyCompactSpace

theorem single_mem (i : Fin 2) (c : ℝ) : Multiplicative.ofAdd (Pi.single i c) ∈ axis i := fun j hj => by simp [hj]

theorem single_int (i : Fin 2) (m : ℤ) : Multiplicative.ofAdd (Pi.single i (m : ℝ)) ∈ intPts := fun j => by
  by_cases h : j = i
  · exact ⟨m, by simp [h]⟩
  · exact ⟨0, by simp [h]⟩

def unitInt (i : Fin 2) : Set (axis i) := {u | u.1.toAdd i ∈ Set.Ico (0 : ℝ) 1}





theorem semiLat_ne_zero {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    {N M Λ : Subgroup G} {ν : Measure N} {π : Measure M} {𝓝 : Set N} {𝓜 : Set M}
    (H : SemiLat N M Λ ν π 𝓝 𝓜) : ν 𝓝 ≠ 0 := by
  haveI := H.haarN
  haveI := H.count
  haveI := H.topGrp
  haveI := H.borel
  haveI : Countable (Λ.subgroupOf N) := Function.Injective.countable
    (f := fun x : Λ.subgroupOf N => (⟨x.1.1, x.2⟩ : Λ)) fun a b h => Subtype.ext (Subtype.ext (congrArg (·.1) h))
  exact H.domN.measure_ne_zero (NeZero.ne ν)

example : IsHt (⊥ : Subgroup (Multiplicative ℝ)) fun g => Real.exp g.toAdd :=
  ⟨fun _ => Real.exp_pos _, Real.continuous_exp.comp continuous_toAdd,
    fun k hk => by rw [Subgroup.mem_bot.1 hk]; simp, fun g => ⟨1, one_mem _, fun x => by simp [Real.exp_add]⟩⟩

theorem fd_one {H : Type} [Group H] [MeasurableSpace H] [MeasurableSingletonClass H] (Λ : Subgroup H) (hΛ : ∀ g, g ∈ Λ)
    (μ : Measure H) : IsFundamentalDomain Λ ({1} : Set H) μ :=
  IsFundamentalDomain.mk' (measurableSet_singleton _).nullMeasurableSet fun x =>
    ⟨⟨x⁻¹, hΛ _⟩, inv_mul_cancel x, fun _ hy => Subtype.ext (eq_inv_of_mul_eq_one_left hy)⟩

theorem haar_count {H : Type} [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H] [MeasurableSpace H]
    [BorelSpace H] : (Measure.count : Measure H).IsHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := inferInstance, toIsMulLeftInvariant := inferInstance,
    open_pos := fun U _ hU h => hU.ne_empty (Measure.count_eq_zero_iff.1 h) }

theorem semiLat_finite {G : Type} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G] [MeasurableSpace G]
    [BorelSpace G] (N M : Subgroup G) [hN : N.Normal] (hd : ∀ g ∈ N, g ∈ M → g = 1) (hs : ∀ g, ∃ u ∈ N, ∃ m ∈ M, g = u * m) :
    SemiLat N M ⊤ Measure.count Measure.count {1} {1} :=
  ⟨isClosed_discrete _, isClosed_discrete _, fun m _ u hu => hN.conj_mem u hu m, hd,
    fun γ _ => let ⟨u, hu, m, hm, e⟩ := hs γ; ⟨u, hu, m, hm, trivial, trivial, e⟩, haar_count, haar_count,
    fd_one _ (fun _ => Subgroup.mem_subgroupOf.2 (Subgroup.mem_top _)) _,
    fd_one _ (fun _ => Subgroup.mem_subgroupOf.2 (Subgroup.mem_top _)) _, by simp, by simp,
    inferInstance, inferInstance, inferInstance⟩

example : letI : TopologicalSpace (Equiv.Perm (Fin 3)) := ⊥; letI : MeasurableSpace (Equiv.Perm (Fin 3)) := ⊤
    SemiLat (alternatingGroup (Fin 3)) (MulAction.stabilizer (Equiv.Perm (Fin 3)) (2 : Fin 3)) ⊤
      Measure.count Measure.count {1} {1} := by
  letI : TopologicalSpace (Equiv.Perm (Fin 3)) := ⊥
  letI : MeasurableSpace (Equiv.Perm (Fin 3)) := ⊤
  haveI : DiscreteTopology (Equiv.Perm (Fin 3)) := ⟨rfl⟩
  haveI : BorelSpace (Equiv.Perm (Fin 3)) := ⟨borel_eq_top_of_discrete.symm⟩
  refine semiLat_finite _ _ ?_ ?_
  · simp only [Equiv.Perm.mem_alternatingGroup, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]; decide
  · simp only [Equiv.Perm.mem_alternatingGroup, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]; decide

end Inhab

end GlobalTheory.ResLine

end
