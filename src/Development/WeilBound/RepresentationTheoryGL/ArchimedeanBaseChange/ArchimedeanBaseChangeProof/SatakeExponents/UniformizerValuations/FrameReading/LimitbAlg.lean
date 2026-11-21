import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbDefs
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ReadLimit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.ConvEqOfIsROp

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev chComm {B : Block E} {Γ : Type} (g : Γ → BGen B) (X : B.Hb →L[ℂ] B.Hb)
    (hg : ∀ x y, Commute (g x).op (g y).op ∧ Commute (g x).op (star (g y).op))
    (hX : ∀ x, Commute X (g x).op ∧ Commute X (star (g x).op)) (hXs : IsSelfAdjoint X) : CommRing (ChAlg g X) :=
  StarAlgebra.adjoinCommRingOfComm ℂ
    (by
      rintro u (⟨x, rfl⟩ | rfl) v (⟨y, rfl⟩ | rfl)
      · exact (hg x y).1
      · exact ((hX x).1).symm
      · exact (hX y).1
      · rfl)
    (by
      rintro u (⟨x, rfl⟩ | rfl) v (⟨y, rfl⟩ | rfl)
      · exact (hg x y).2
      · rw [hXs.star_eq]; exact ((hX x).1).symm
      · exact (hX y).2
      · rw [hXs.star_eq])

def genO {B : Block E} {Γ : Type} (g : Γ → BGen B) (X : B.Hb →L[ℂ] B.Hb) : Option Γ → (B.Hb →L[ℂ] B.Hb) :=
  fun o => o.elim X fun x => (g x).op

theorem range_genO {B : Block E} {Γ : Type} (g : Γ → BGen B) (X : B.Hb →L[ℂ] B.Hb) :
    Set.range (genO g X) = gOps g ∪ {X} := by
  ext z
  constructor
  · rintro ⟨o, rfl⟩
    cases o with
    | none => exact Or.inr rfl
    | some x => exact Or.inl ⟨x, rfl⟩
  · rintro (⟨x, rfl⟩ | rfl)
    · exact ⟨some x, rfl⟩
    · exact ⟨none, rfl⟩

def letter {B : Block E} {Γ : Type} (g : Γ → BGen B) (tX : PT B) : Option Γ × Bool → BGen B
  | (none, false) => Sum.inr tX
  | (none, true) => Sum.inr tX.adj
  | (some x, false) => g x
  | (some x, true) => (g x).adj

theorem letter_ok (hO : BlockOperatorsProductAdjoint) (hW : BlockWordOperators) {B : Block E} {Γ : Type} (g : Γ → BGen B)
    (X : B.Hb →L[ℂ] B.Hb) (tX t₀ : PT B) (hg : ∀ x, (g x).Ok) (htX : tX.Ok) (hX : X = tX.op) (h₀ : t₀.Ok)
    (p : Option Γ × Bool) :
    (letter g tX p).Ok ∧ (letter g tX p).op = if p.2 then star (genO g X p.1) else genO g X p.1 := by
  have hadj := (hW E B [] t₀ 0 (by simp) h₀ le_rfl (by simp)).2.2.2.2.1
  obtain ⟨o, s⟩ := p
  cases o with
  | none =>
    cases s with
    | false => exact ⟨htX, hX.symm⟩
    | true =>
      have := hO E B tX tX htX htX
      refine ⟨this.2.2.2.2.1, ?_⟩
      show tX.adj.op = star X
      rw [this.2.2.2.2.2.1, hX, ContinuousLinearMap.star_eq_adjoint]
  | some x =>
    cases s with
    | false => exact ⟨hg x, rfl⟩
    | true =>
      refine ⟨(hadj (g x) (hg x)).1, ?_⟩
      show (g x).adj.op = star (g x).op
      rw [(hadj (g x) (hg x)).2, ContinuousLinearMap.star_eq_adjoint]

theorem phiEx (hO : BlockOperatorsProductAdjoint) (hW : BlockWordOperators) (hS : BlockLinearCombinations) (hA : AdjWords) {B : Block E} {Γ : Type} (g : Γ → BGen B)
    (X : B.Hb →L[ℂ] B.Hb) (tX t₀ : PT B) (hg : ∀ x, (g x).Ok) (htX : tX.Ok) (hX : X = tX.op) (h₀ : t₀.Ok)
    (y : ChAlg g X) : ∃ Φ : Matrix B.I B.I (H E B.a B.b → ℂ), IsTestM Φ ∧ IsROp B.D Φ ((y : B.Hb →L[ℂ] B.Hb) * t₀.op) := by
  have hy : (y : B.Hb →L[ℂ] B.Hb) ∈ StarAlgebra.adjoin ℂ (Set.range (genO g X)) := by
    rw [range_genO]; exact y.2
  obtain ⟨J, hJ, c, w, L, -, hyw, -⟩ := hA (B.Hb →L[ℂ] B.Hb) (Option Γ) (genO g X) _ hy
  have hl := letter_ok hO hW g X tX t₀ hg htX hX h₀

  let bw : J → List (BGen B) := fun j => (w j).map (letter g tX)
  have bok : ∀ j, ∀ b ∈ bw j, b.Ok := fun j b hb => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hb
    exact (hl p).1
  have bop : ∀ j, ((bw j).map BGen.op).prod = wdVal (genO g X) (w j) := fun j => by
    simp only [bw, wdVal, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    exact (hl p).2
  let R : J → ℝ := fun j => ((bw j).map fun b => Sum.elim (fun _ => (0 : ℝ)) (fun s => |s.T| + |s.r + B.c|) b).sum
  have hR0 : ∀ j, 0 ≤ R j := fun j => by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hz
    rcases b with _ | s
    · exact le_rfl
    · exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hRs : ∀ j, ∀ s, Sum.inr s ∈ bw j → s.T ≤ R j ∧ s.r + B.c ≤ R j := fun j s hs => by
    have hle : |s.T| + |s.r + B.c| ≤ R j := by
      have := List.single_le_sum (l := (bw j).map fun b => Sum.elim (fun _ => (0 : ℝ)) (fun s => |s.T| + |s.r + B.c|) b)
        (fun z hz => by
          obtain ⟨b, -, rfl⟩ := List.mem_map.1 hz
          rcases b with _ | s
          · exact le_rfl
          · exact add_nonneg (abs_nonneg _) (abs_nonneg _))
        _ (List.mem_map.2 ⟨Sum.inr s, hs, rfl⟩)
      exact this
    exact ⟨(le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans hle),
      (le_abs_self _).trans ((le_add_of_nonneg_left (abs_nonneg _)).trans hle)⟩
  have hwd := fun j => hW E B (bw j) t₀ (R j) (bok j) h₀ (hR0 j) (hRs j)
  have hsum := hS E B.a B.b B.D B.I J Finset.univ (fun j => c j * BGen.sc (bw j)) (fun j => (BGen.wd (bw j) t₀).Φ)
    (fun j => (BGen.wd (bw j) t₀).op) (fun j _ => by
      have := hO E B _ _ (hwd j).1 (hwd j).1
      exact ⟨this.1, this.2.1⟩)
  refine ⟨_, hsum.1, ?_⟩
  convert hsum.2 using 1
  rw [hyw, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_assoc, ← bop, (hwd j).2.1, smul_smul]

end PositivityTheory.Rg.BcB.F.Rd

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd.B

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rd

theorem bsG' (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩

theorem bsF' (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : BorelSpace (Hf E a b) := ⟨rfl⟩

attribute [local instance] bsG' bsF'

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Real

variable {B : Block E} {Γ : Type} (g : Γ → BGen B) (X : B.Hb →L[ℂ] B.Hb) (t₀ : PT B)

def phiG (x : ChAlg g X) : Matrix B.I B.I (H E B.a B.b → ℂ) :=
  if h : ∃ Φ : Matrix B.I B.I (H E B.a B.b → ℂ), IsTestM Φ ∧ IsROp B.D Φ ((x : B.Hb →L[ℂ] B.Hb) * t₀.op) then
    h.choose
  else 0

theorem mul_facts (hTM : TensMul) (hBO : BlockOperatorsProductAdjoint) (t : PT B) (ht : t.Ok) (ht₀ : t₀.Ok) :
    IsTestM (mulM B.D.μ t.Φ t₀.Φ) ∧ IsROp B.D (mulM B.D.μ t.Φ t₀.Φ) (t.op * t₀.op) := by
  haveI := B.ha; haveI := B.hb; haveI := B.hν
  have hm := hTM E B.a B.b B.D B.μa B.μb B.ν B.Ma B.Mb B.κ t.ka t₀.ka t.kb t₀.kb t.va t₀.va t.vb t₀.vb t.T t₀.T t.ψ t₀.ψ
      B.compat ht.ka ht.kb ht₀.ka ht₀.kb ht.ψ ht₀.ψ
  have hΦ : mulM B.D.μ t.Φ t₀.Φ = (t.mul t₀).Φ := hm.2
  obtain ⟨-, -, hok, hop, -⟩ := hBO E B t t₀ ht ht₀
  have h2 := hBO E B (t.mul t₀) (t.mul t₀) hok hok
  rw [hΦ, ← hop]
  exact ⟨h2.1, h2.2.1⟩

theorem ok_of_inr {t : PT B} {y : Γ} (hok : ∀ x, (g x).Ok) (hy : g y = Sum.inr t) : t.Ok := by
  have := hok y
  rw [hy] at this
  exact this

set_option maxHeartbeats 1000000 in
theorem realise_commuting_family (hE2 : E2) (hTM : TensMul) (hBO : BlockOperatorsProductAdjoint) (hBW : BlockWordOperators) (hBS : BlockLinearCombinations) (hAW : AdjWords)
    [Countable Γ] (a₀ : Γ) (tX : PT B) (χ : ChAlg g X →⋆ₐ[ℂ] ℂ)
    (hok : ∀ x, (g x).Ok) (htX : tX.Ok) (hXe : X = tX.op) (ha₀ : g a₀ = Sum.inr t₀)
    (hc : ∀ x y, Commute (g x).op (g y).op ∧ Commute (g x).op (star (g y).op))
    (hXc : ∀ x, Commute X (g x).op ∧ Commute X (star (g x).op)) (hXs : IsSelfAdjoint X)
    (hχ : ∀ y, ‖χ y‖ ≤ ‖(y : B.Hb →L[ℂ] B.Hb)‖) (hχ0 : χ (genE g X a₀) ≠ 0) :
    ∃ (M : ℕ) (s : ℕ → ChAlg g X → ℂ) (f : ℕ → B.I → H E B.a B.b → ℂ),
      (∀ y, Tendsto (fun k => s k (genE g X y)) atTop (𝓝 (χ (genE g X y)))) ∧
      Tendsto (fun k => s k (XE g X)) atTop (𝓝 (χ (XE g X))) ∧
      ∀ k, s k (genE g X a₀) ≠ 0 ∧ (∀ i, Continuous (f k i)) ∧ f k ≠ 0 ∧ LeftInv (f k) ∧ WL2 B.D M (f k) ∧
        PositivityTheory.Rg.BcB.E.conv B.D.μ t₀.Φ (f k) = s k (genE g X a₀) • f k ∧
        (∀ y (t : PT B), g y = Sum.inr t →
          PositivityTheory.Rg.BcB.E.conv B.D.μ (mulM B.D.μ t.Φ t₀.Φ) (f k) = (s k (genE g X y) * s k (genE g X a₀)) • f k) ∧
        PositivityTheory.Rg.BcB.E.conv B.D.μ (mulM B.D.μ tX.Φ t₀.Φ) (f k) = (s k (XE g X) * s k (genE g X a₀)) • f k := by
  have ht₀ : t₀.Ok := ok_of_inr g hok ha₀
  have ea : ((genE g X a₀ : ChAlg g X) : B.Hb →L[ℂ] B.Hb) = t₀.op := by
    show (g a₀).op = _
    rw [ha₀]
    rfl
  have hspec : ∀ x : ChAlg g X, IsTestM (phiG g X t₀ x) ∧ IsROp B.D (phiG g X t₀ x) ((x : B.Hb →L[ℂ] B.Hb) * t₀.op) :=
    fun x => by
      have h := phiEx hBO hBW hBS hAW g X tX t₀ hok htX hXe ht₀ x
      unfold phiG
      rw [dif_pos h]
      exact h.choose_spec
  letI : CommRing (ChAlg g X) := chComm g X hc hXc hXs
  have hCc : ({1} ∪ Set.range (genE g X) ∪ {XE g X} : Set (ChAlg g X)).Countable :=
    ((Set.countable_singleton _).union (Set.countable_range _)).union (Set.countable_singleton _)
  obtain ⟨M, s, f, hlim, hk⟩ := hE2 E B.a B.b B.D B.I B.Hb (ContinuousLinearMap.id ℂ B.Hb) (fun v => rfl) (ChAlg g X)
    (StarSubalgebra.subtype _) χ (genE g X a₀) ({1} ∪ Set.range (genE g X) ∪ {XE g X}) (phiG g X t₀) hχ hχ0 hCc
    (Or.inl (Or.inl rfl)) (fun x => (hspec x).1) (fun x => ⟨_, (hspec x).2, fun v => by
      change ((x : B.Hb →L[ℂ] B.Hb) * t₀.op) v =
        ((x : B.Hb →L[ℂ] B.Hb) * ((genE g X a₀ : ChAlg g X) : B.Hb →L[ℂ] B.Hb)) v
      rw [ea], fun u hu => by
      have hu0 : u = 0 := inner_self_eq_zero.1 (hu u)
      rw [hu0, map_zero]⟩)
  refine ⟨M, fun k x => s k x, f, fun y => hlim _ (Or.inl (Or.inr ⟨y, rfl⟩)), hlim _ (Or.inr rfl), fun k => ?_⟩
  obtain ⟨h0, hcont, hne, hL, hW, hconv⟩ := hk k
  have key : ∀ x ∈ ({1} ∪ Set.range (genE g X) ∪ {XE g X} : Set (ChAlg g X)), ∀ Ψ, IsTestM Ψ →
      IsROp B.D Ψ ((x : B.Hb →L[ℂ] B.Hb) * t₀.op) →
      PositivityTheory.Rg.BcB.E.conv B.D.μ Ψ (f k) = s k (x * genE g X a₀) • f k := fun x hx Ψ h1 h2 =>
    (PositivityTheory.Rg.BcB.E2.conv_eq_of_isROp B.D h1 (hspec x).1 h2 (hspec x).2 hcont hL).trans (hconv x hx)
  refine ⟨h0, hcont, hne, hL, hW, ?_, fun y t hy => ?_, ?_⟩
  · have h0' := hBO E B t₀ t₀ ht₀ ht₀
    have h := key 1 (Or.inl (Or.inl rfl)) t₀.Φ h0'.1 (by
      show IsROp B.D t₀.Φ (1 * t₀.op)
      rw [one_mul]
      exact h0'.2.1)
    rw [one_mul] at h
    exact h
  · have ht := ok_of_inr g hok hy
    have hm := mul_facts t₀ hTM hBO t ht ht₀
    have e : ((genE g X y : ChAlg g X) : B.Hb →L[ℂ] B.Hb) = t.op := by
      show (g y).op = _
      rw [hy]
      rfl
    have h := key (genE g X y) (Or.inl (Or.inr ⟨y, rfl⟩)) _ hm.1 (by rw [e]; exact hm.2)
    rw [map_mul] at h
    exact h
  · have hm := mul_facts t₀ hTM hBO tX htX ht₀
    have e : ((XE g X : ChAlg g X) : B.Hb →L[ℂ] B.Hb) = tX.op := hXe
    have h := key (XE g X) (Or.inr rfl) _ hm.1 (by rw [e]; exact hm.2)
    rw [map_mul] at h
    exact h

end Real

theorem realise (hE2 : E2) (hTM : TensMul) (hBO : BlockOperatorsProductAdjoint) (hBW : BlockWordOperators) (hBS : BlockLinearCombinations) (hAW : AdjWords) :
    RealiseSt := by
  intro E _ _ _ B Γ _ g a₀ t₀ X tX χ hok htX hXe ha₀ hc hXc hXs hχ hχ0
  exact realise_commuting_family g X t₀ hE2 hTM hBO hBW hBS hAW a₀ tX χ hok htX hXe ha₀ hc hXc hXs hχ hχ0

end PositivityTheory.Rg.BcB.F.Rd.B

end
end
