import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.Enlarge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SmallTendsto
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.MuInf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.CuspCaseJ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.PartNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.SigmaEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.AsmThOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.CtEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.MuConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RegCt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.LevelFn
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.ExistsUnitOrdLEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.GeneralLocalHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.InertLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RChoice
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RUEval
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RFamMatch
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.EvaluationCombinedTestFunction
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.ConstantTermParabolicAverage
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrinkAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.TypeSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.RtEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.SliceT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.TyComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.EigTOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.CuspMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.NormTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.NormUniq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.SatComb
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.SplitLim
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.FullThetaHolds

section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem satEig_rev_of_stable {q n : ℕ} {B : Multiset ℂˣ} (hB : B.card = n) (hs : inv B = B)
    (i : Fin (n + 1)) : satEig q n B (i.rev : ℕ) = satEig q n B n * satEig q n B (i : ℕ) := by
  have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
  have h := GlobalTheory.LFun.ConjPlace.satEig_inv_mul (q := q) hB hi
  have hs' : B.map (·⁻¹) = B := hs
  rw [hs'] at h
  have hr : (i.rev : ℕ) = n - (i : ℕ) := by
    rw [Fin.val_rev]; omega
  rw [hr, ← h, mul_comm]

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.hecke_eigenvalues_unitary_one_factor :
    EvaluationAtUnitaryOne := by
  intro E _ _ _ w a b e he B₁ B₂ h₁ h₂ s₁ s₂
  induction he with
  | one => simp [ev2, Ex.ev]
  | step c p =>
    have r₁ := satEig_rev_of_stable (q := qV E w) h₁ s₁ p.1
    have r₂ := satEig_rev_of_stable (q := qV E w) h₂ s₂ p.2
    simp only [ev2, Ex.ev, dEx, Fin.val_last, r₁, r₂]
    ring
  | mul _ _ ih₁ ih₂ =>
    simp only [ev2, Ex.ev] at ih₁ ih₂ ⊢
    rw [ih₁, ih₂, one_mul]
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem inv_eq_of_eig {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) {n : ℕ}
    {B : Multiset ℂˣ} (hB : B.card = n)
    (h : ∀ i ≤ n, satEig (qV E w) n B n * satEig (qV E w) n B i = satEig (qV E w) n B (n - i)) :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.inv B = B := by
  have hne : satEig (qV E w) n B n ≠ 0 := GlobalTheory.LFun.SatCompare.satEig_self_ne_zero hB
  have hI : (UpperTheory.V.Z.Tf.GlobalTraceComparison.inv B).card = n := by simpa [UpperTheory.V.Z.Tf.GlobalTraceComparison.inv] using hB
  refine eq_of_satEig_eq (qV_ne_zero w) hI hB fun j hj => ?_
  have e := GlobalTheory.LFun.ConjPlace.satEig_inv_mul (q := qV E w) hB hj
  rw [← h j hj, mul_comm] at e
  exact mul_left_cancel₀ hne e

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.unitary_one_characters_separated_by_eigenvalues :
    SeparatesUnitaryOne := by
  intro E _ _ _ w a b B₁ B₂ h₁ h₂ hns
  by_cases hz : ∀ p : Fin (a + 1) × Fin (b + 1), ev2 a b w (dEx p) B₁ B₂ = 0
  · exfalso
    have hs₁ : satEig (qV E w) a B₁ a ≠ 0 := GlobalTheory.LFun.SatCompare.satEig_self_ne_zero h₁
    have hs₂ : satEig (qV E w) b B₂ b ≠ 0 := GlobalTheory.LFun.SatCompare.satEig_self_ne_zero h₂
    have key : ∀ p : Fin (a + 1) × Fin (b + 1),
        satEig (qV E w) a B₁ a * satEig (qV E w) b B₂ b *
            (satEig (qV E w) a B₁ p.1 * satEig (qV E w) b B₂ p.2) =
          satEig (qV E w) a B₁ (a - p.1) * satEig (qV E w) b B₂ (b - p.2) := by
      intro p
      have := hz p
      simp only [ev2, dEx, Ex.ev, Fin.val_last, Fin.val_rev] at this
      have e₁ : a + 1 - ((p.1 : ℕ) + 1) = a - p.1 := by omega
      have e₂ : b + 1 - ((p.2 : ℕ) + 1) = b - p.2 := by omega
      rw [e₁, e₂] at this
      linear_combination this
    refine hns ⟨inv_eq_of_eig w h₁ fun i hi => ?_, inv_eq_of_eig w h₂ fun j hj => ?_⟩
    · have := key (⟨i, Nat.lt_succ_of_le hi⟩, 0)
      simp only [Fin.val_zero, GlobalTheory.LFun.ConjPlace.satEig_zero, mul_one, Nat.sub_zero] at this
      refine mul_right_cancel₀ hs₂ ?_
      linear_combination this
    · have := key (0, ⟨j, Nat.lt_succ_of_le hj⟩)
      simp only [Fin.val_zero, GlobalTheory.LFun.ConjPlace.satEig_zero, one_mul, Nat.sub_zero] at this
      refine mul_left_cancel₀ hs₁ ?_
      linear_combination this
  · push_neg at hz
    obtain ⟨p, hp⟩ := hz
    refine ⟨_, U1.step (-(ev2 a b w (dEx p) B₁ B₂)⁻¹) p, ?_⟩
    have e : ev2 a b w (Ex.add Ex.one (Ex.smul (-(ev2 a b w (dEx p) B₁ B₂)⁻¹) (dEx p))) B₁ B₂ =
        1 + -(ev2 a b w (dEx p) B₁ B₂)⁻¹ * ev2 a b w (dEx p) B₁ B₂ := rfl
    rw [e, neg_mul, inv_mul_cancel₀ hp]
    ring
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.endoS :
    Enlarge → Places → EndoBlockG → EndoBlockS := by
  intro hEn hP hG E _ _ _ hunr a b hab S hS l₁ l₂ Z hZ φ hφ hreg
  obtain ⟨J, _, D₁, D₂, B₁, B₂, hSat, hInf, hGr⟩ := hG E hunr a b hab S hS l₁ l₂ Z hZ φ hφ hreg
  have hoff : ∀ w : Pl E, ¬ IsSplitAt w → Off Z w := fun w hw => by
    have hc : cPl w = w := by
      by_contra h
      exact hw (((hP E).2.1 w).2.2 h)
    have hz : w ∉ Z := fun h => hw (hZ w h).2
    exact ⟨hz, by rw [hc]; exact hz⟩
  let St : J → Prop := fun j =>
    ∀ w : Pl E, ¬ IsSplitAt w → inv (B₁ j w) = B₁ j w ∧ inv (B₂ j w) = B₂ j w
  have hu : ∀ i : {j // ¬ St j}, ∃ w : Pl E, ¬ IsSplitAt w ∧
      ¬ (inv (B₁ i.1 w) = B₁ i.1 w ∧ inv (B₂ i.1 w) = B₂ i.1 w) := fun i => by
    by_contra h
    exact i.2 fun w hw => by_contra fun h' => h ⟨w, hw, h'⟩
  choose u hu₁ hu₂ using hu
  classical
  refine ⟨{j // St j}, inferInstance, fun j => D₁ j.1, fun j => D₂ j.1, fun j => B₁ j.1, fun j => B₂ j.1,
    fun j w h => hSat j.1 w h, fun j => hInf j.1, fun j w h => j.2 w h, ?_⟩
  intro T hT hTZ e₁ e₂ ρ hρ hlt
  obtain ⟨T', e₁', e₂', hT'S, hT'Z, hone, hzero, hval, hgeom⟩ :=
    hEn E hunr a b S hS Z T hZ hT hTZ e₁ e₂ {j // ¬ St j} u (fun i => B₁ i.1) (fun i => B₂ i.1) fun i =>
      ⟨hu₁ i, sat_card (hSat i.1 (u i) (hoff _ (hu₁ i))).1, sat_card (hSat i.1 (u i) (hoff _ (hu₁ i))).2, hu₂ i⟩
  have hsm := hGr T' hT'S hT'Z e₁' e₂' ρ hone hρ fun j => by
    by_cases hj : St j
    · rw [hval (B₁ j) (B₂ j) fun i =>
        ⟨sat_card (hSat j (u i) (hoff _ (hu₁ i))).1, sat_card (hSat j (u i) (hoff _ (hu₁ i))).2,
          (hj (u i) (hu₁ i)).1, (hj (u i) (hu₁ i)).2⟩]
      exact hlt ⟨j, hj⟩
    · have h0 := hzero ⟨j, hj⟩
      simp only at h0
      rw [h0, norm_zero]
      exact hρ
  simpa only [hgeom] using hsm
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.stableS :
    Enlarge → Places → StableBlockG → StableBlockS := by
  classical
  intro hEn hP hG E _ _ _ hunr n hn π hreg hd
  obtain ⟨l₁, hl⟩ := hG E hunr n hn π hreg hd
  refine ⟨l₁, fun l₂ S hS Z hZ B τ hB hτ => ?_⟩
  obtain ⟨c, hc, hst⟩ := hl l₂ S hS Z hZ B τ hB hτ
  refine ⟨c, hc, fun φ hφ hr => ?_⟩
  obtain ⟨J, _, D, B₁, hD, hInf, hbd⟩ := hst φ hφ hr

  have hoff : ∀ w : Pl E, ¬ IsSplitAt w → Off Z w := by
    intro w hw
    have hcw : cPl w = w := by
      by_contra h
      exact hw (((hP E).2.1 w).2.2 h)
    have hwZ : w ∉ Z := fun h => hw (hZ w h).2
    exact ⟨hwZ, by rwa [hcw]⟩

  let good : J → Prop := fun j => ∀ w, ¬ IsSplitAt w → inv (B w) = B w → inv (B₁ j w) = B₁ j w
  refine ⟨{j // good j}, inferInstance, fun j => D j.1, fun j => B₁ j.1, fun j => hD j.1, fun j => hInf j.1,
    fun j => j.2, ?_⟩
  intro T hT hTZ e₁ e₂ ρ hρ hlt
  have hbad : ∀ i : {j // ¬ good j}, ∃ w, ¬ IsSplitAt w ∧ inv (B w) = B w ∧ inv (B₁ i.1 w) ≠ B₁ i.1 w := by
    intro i
    have h := i.2
    simp only [good, not_forall] at h
    obtain ⟨w, h1, h2, h3⟩ := h
    exact ⟨w, h1, h2, h3⟩
  choose u hu1 hu2 hu3 using hbad
  have hcard : ∀ j w, ¬ IsSplitAt w → (B₁ j w).card = n := fun j w hw => sat_card ((hD j).2 w (hoff w hw))
  have hBcard : ∀ w, ¬ IsSplitAt w → (B w).card = n := fun w hw => (hB w (hoff w hw)).card
  obtain ⟨T', e₁', e₂', hT'S, hT'Z, hT'e, hzero, hval, hgeom⟩ :=
    hEn E hunr n 0 S hS Z T hZ hT hTZ e₁ e₂ {j // ¬ good j} u (fun i => B₁ i.1) (fun _ => 0)
      (fun i => ⟨hu1 i, hcard _ _ (hu1 i), Multiset.card_zero, fun h => hu3 i h.1⟩)
  have hvj : ∀ j, good j → val T' e₁' e₂' (B₁ j) 0 = val T e₁ e₂ (B₁ j) 0 := fun j hj =>
    hval (B₁ j) 0 fun i => ⟨hcard _ _ (hu1 i), Multiset.card_zero, hj _ (hu1 i) (hu2 i), Multiset.map_zero _⟩
  have hvB : val T' e₁' e₂' B 0 = val T e₁ e₂ B 0 :=
    hval B 0 fun i => ⟨hBcard _ (hu1 i), Multiset.card_zero, hu2 i, Multiset.map_zero _⟩
  have hsm := hbd T' hT'S hT'Z e₁' e₂' ρ hT'e hρ fun j => by
    by_cases hj : good j
    · rw [hvj j hj]
      exact hlt ⟨j, hj⟩
    · have h0 : val T' e₁' e₂' (B₁ j) 0 = 0 := hzero ⟨j, hj⟩
      rw [h0, norm_zero]
      exact hρ
  simpa only [hgeom, hvB] using hsm
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.mwAt :
    MWAt := by
  intro E _ _ _ n l v
  have hne : ComplexEmbedding.conjugate v.embedding ≠ v.embedding := fun h =>
    (InfinitePlace.isComplex_iff.1 (NumberField.IsTotallyComplex.isComplex v))
      (ComplexEmbedding.isReal_iff.2 h)
  have hmk : InfinitePlace.mk (ComplexEmbedding.conjugate v.embedding) = v := by
    rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  constructor
  · unfold mW PositivityTheory.Rg.BcB.CG.mOf infOfWeight PositivityTheory.RgBcC.infOf
    simp only [InfinitePlace.mk_embedding, decide_true, if_true, one_mul]
    congr 1
    funext k
    rw [add_sub_assoc]
  · unfold mW PositivityTheory.Rg.BcB.CG.mOf infOfWeight PositivityTheory.RgBcC.infOf
    simp only [hmk, hne, decide_false, Multiset.map_map]
    congr 1
    funext k
    simp only [Function.comp, Bool.false_eq_true, if_false]
    ring
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.dualWt :
    DualWt := fun _ lam => ⟨lam.dual, GlobalTheory.DefiniteBC.infOfWeight_dual lam⟩
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.absInf :
    AbsInf := by
  intro E _ _ _ N P z τ
  have key : (P.twist (Model.absC E z)).infChar τ = (P.infChar τ).map (· + z) := by
    have e := ((ParLaws.hasInfChar_infChar P τ).twist (Model.absC E z)).infChar_eq
    rw [Model.expo_absC] at e
    exact e
  exact ⟨key, key⟩
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem rel_comp {r s t : ℂ → ℂ → Prop} (h : ∀ x y z, r x y → s y z → t x z)
    {a b c : Multiset ℂ} (hab : Multiset.Rel r a b) :
    Multiset.Rel s b c → Multiset.Rel t a c := by
  induction hab generalizing c with
  | zero =>
    intro h0
    rw [Multiset.rel_zero_left] at h0
    subst h0
    exact Multiset.Rel.zero
  | cons hxy _ ih =>
    intro hc
    obtain ⟨z, zs, hz, hzs, rfl⟩ := Multiset.rel_cons_left.1 hc
    exact Multiset.Rel.cons (h _ _ _ hxy hz) (ih hzs)

private theorem exists_sep (S : Finset (ℂ × ℂ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ S, p.1 ≠ p.2 → ε < ‖p.1 - p.2‖ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert p S _ ih =>
    obtain ⟨ε, h0, hε⟩ := ih
    by_cases hp : p.1 = p.2
    · refine ⟨ε, h0, fun q hq hne => ?_⟩
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact absurd hp hne
      · exact hε q hq hne
    · have hpos : 0 < ‖p.1 - p.2‖ := norm_pos_iff.2 (sub_ne_zero.2 hp)
      refine ⟨min ε (‖p.1 - p.2‖ / 2), lt_min h0 (half_pos hpos), fun q hq hne => ?_⟩
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact (min_le_right _ _).trans_lt (half_lt_self hpos)
      · exact (min_le_left _ _).trans_lt (hε q hq hne)

private theorem eq_of_rel {a b : Multiset ℂ}
    (h : ∀ ε : ℝ, 0 < ε → Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) a b) : a = b := by
  classical
  obtain ⟨ε, h0, hε⟩ := exists_sep (a.toFinset ×ˢ b.toFinset)
  refine Multiset.rel_eq.1 ((h ε h0).mono fun x hx y hy hxy => ?_)
  by_contra hne
  exact absurd hxy (not_le.2 (hε (x, y) (by simp [hx, hy]) hne))

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.mtoLaws :
    MToLaws := by
  intro E _ _ _
  refine ⟨fun m x y hx hy => ?_, fun m x z z₀ hx hz τ ε hε => ?_,
    fun m m' x x' hx hx' τ ε hε => ?_⟩
  · funext τ
    refine eq_of_rel fun ε hε => ?_
    obtain ⟨k, h1, h2⟩ := ((hx τ (ε / 2) (half_pos hε)).and (hy τ (ε / 2) (half_pos hε))).exists
    refine rel_comp (fun p q w (hpq : ‖q - p‖ ≤ ε / 2) (hqw : ‖q - w‖ ≤ ε / 2) => ?_)
      (Multiset.rel_flip.2 h1) h2
    calc ‖p - w‖ = ‖(q - w) - (q - p)‖ := by congr 1; ring
      _ ≤ ‖q - w‖ + ‖q - p‖ := norm_sub_le _ _
      _ ≤ ε := by linarith
  · have hz' : ∀ᶠ k in atTop, ‖z k - z₀‖ ≤ ε / 2 :=
      (Metric.tendsto_nhds.1 hz (ε / 2) (half_pos hε)).mono fun k hk => by
        rw [dist_eq_norm] at hk
        exact hk.le
    filter_upwards [hx τ (ε / 2) (half_pos hε), hz'] with k h1 h2
    refine Multiset.rel_map.2 (h1.mono fun p _ q _ hpq => ?_)
    calc ‖(p + z k) - (q + z₀)‖ = ‖(p - q) + (z k - z₀)‖ := by congr 1; ring
      _ ≤ ‖p - q‖ + ‖z k - z₀‖ := norm_add_le _ _
      _ ≤ ε := by linarith
  · filter_upwards [hx τ ε hε, hx' τ ε hε] with k h1 h2
    exact h1.add h2
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.cdAddG :
    CDAddG := by
  intro E _ _ _ r s D₁ D₂ ν ν' hr hs
  let e : Fin (D₁.c + D₂.c) ≃ Fin D₁.c ⊕ Fin D₂.c := finSumFinEquiv.symm
  let Q : Fin D₁.c ⊕ Fin D₂.c → Σ k, CG E k := Sum.elim (fun i => ⟨_, (D₁.P i).twist ν⟩) fun i => ⟨_, (D₂.P i).twist ν'⟩
  refine ⟨⟨D₁.c + D₂.c, fun i => (Q (e i)).1, fun i => (Q (e i)).2, fun i => ?_, ?_⟩, fun π hπ => ?_,
    fun w B₁ B₂ h h' ⟨b₁, c₁, d₁⟩ ⟨b₂, c₂, d₂⟩ => ⟨fun i => Sum.elim (fun i => (b₁ i).map (· * ν.val w))
      (fun i => (b₂ i).map (· * ν'.val w)) (e i), fun i : Fin (D₁.c + D₂.c) => ?_, ?_⟩, fun τ => ?_⟩
  · rcases e i with i | i
    exacts [D₁.pos i, D₂.pos i]
  · rw [e.sum_comp fun o => (Q o).1, Fintype.sum_sum_type]
    exact congrArg₂ (· + ·) D₁.sum D₂.sum
  · obtain ⟨i, hi⟩ := hπ
    have h1 : (Q (e i)).1 = r + s := congrArg Sigma.fst hi
    revert h1
    rcases e i with i | i
    · intro h1
      have h2 : D₁.N i ≤ r := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans D₁.sum.le
      have h3 : D₁.N i = r + s := h1
      omega
    · intro h1
      have h2 : D₂.N i ≤ s := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans D₂.sum.le
      have h3 : D₂.N i = r + s := h1
      omega
  · show (Q (e i)).2.HasSat w (Sum.elim (fun i => (b₁ i).map (· * ν.val w)) (fun i => (b₂ i).map (· * ν'.val w)) (e i))
    rcases e i with i | i
    exacts [PositivityTheory.RgJS.satake_twist_holds E _ _ _ w _ h (c₁ i), PositivityTheory.RgJS.satake_twist_holds E _ _ _ w _ h' (c₂ i)]
  · show ∑ i : Fin (D₁.c + D₂.c), _ = _
    rw [e.sum_comp (Sum.elim (fun i => (b₁ i).map (· * ν.val w)) fun i => (b₂ i).map (· * ν'.val w)), Fintype.sum_sum_type,
      ← d₁, ← d₂]
    exact congrArg₂ (· + ·) (map_sum (Multiset.mapAddMonoidHom _) _ _).symm (map_sum (Multiset.mapAddMonoidHom _) _ _).symm
  · show ∑ i : Fin (D₁.c + D₂.c), (Q (e i)).2.infChar τ = _
    rw [e.sum_comp fun o => (Q o).2.infChar τ, Fintype.sum_sum_type]
    rfl
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.ctCaseJ :
    StepT → SplitLim → SatComb → CDAddG → AbsInf → MToLaws → CtCaseJ := by
  intro hS hL hC hA hI hM E _ _ _ r s hr hs bad ih₁ ih₂ K W m₀ X hK hW
  obtain ⟨K₁, W₁, K₂, W₂, l₁, f₁, l₂, f₂, hS⟩ := hS E r s bad K W hK hW
  obtain ⟨T, hT⟩ := hL E m₀ ((-((s : ℝ) / 2) : ℝ) : ℂ) (((r : ℝ) / 2 : ℝ) : ℂ)
  choose J₁ i₁ D₁ C₁ a₁ b₁ using fun p : T => ih₁ K₁ W₁ p.1.1 l₁ f₁
  choose J₂ i₂ D₂ C₂ a₂ b₂ using fun p : T => ih₂ K₂ W₂ p.1.2 l₂ f₂
  have hν := fun x : ℝ => GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) x
  choose D d₁ d₂ d₃ using fun j : Σ p : T, J₁ p × J₂ p => hA E r s (D₁ j.1 j.2.1) (D₂ j.1 j.2.2)
    (GlobalTheory.Mem.Chr.CharModel.absChar E ((-((s : ℝ) / 2) : ℝ) : ℂ)) (GlobalTheory.Mem.Chr.CharModel.absChar E (((r : ℝ) / 2 : ℝ) : ℂ)) hr hs
  refine ⟨Σ p : T, J₁ p × J₂ p, inferInstance, D, _, fun j => ⟨fun π _ => d₁ j π, fun w hw =>
    d₂ j w _ _ ((hν _).1 w) ((hν _).1 w) ((a₁ j.1 j.2.1).2 w hw) ((a₂ j.1 j.2.2).2 w hw)⟩, fun φ m B h hm => ?_⟩
  choose φ₁ φ₂ m₁ m₂ B₁ B₂ e₁ e₂ e₃ e₄ using fun k => hS (φ k) (m k) (B k) (h k).1 (h k).2
  obtain ⟨p, hp, σ, hσ, t₁, t₂⟩ := hT m m₁ m₂ e₃ hm
  obtain ⟨j₁, σ₁, hσ₁, v₁, u₁⟩ := b₁ ⟨p, hp⟩ (fun k => φ₁ (σ k)) _ (fun k => B₁ (σ k)) (fun k => ⟨e₁ _, trivial⟩) t₁
  obtain ⟨j₂, σ₂, hσ₂, v₂, u₂⟩ := b₂ ⟨p, hp⟩ (fun k => φ₂ (σ (σ₁ k))) (fun k => m₂ (σ (σ₁ k))) (fun k => B₂ (σ (σ₁ k)))
    (fun k => ⟨e₂ _, trivial⟩) fun τ ε hε => hσ₁.tendsto_atTop.eventually (t₂ τ ε hε)
  have h₀ : m₀ = fun t => (p.1 t).map (· + ((-((s : ℝ) / 2) : ℝ) : ℂ)) + (p.2 t).map (· + (((r : ℝ) / 2 : ℝ) : ℂ)) := by
    obtain ⟨hu, hsh, hadd⟩ := hM E
    have c₁ := hsh _ _ (fun _ => ((-((s : ℝ) / 2) : ℝ) : ℂ)) _ t₁ tendsto_const_nhds
    have c₂ := hsh _ _ (fun _ => (((r : ℝ) / 2 : ℝ) : ℂ)) _ t₂ tendsto_const_nhds
    have c₃ := hadd _ _ _ _ c₁ c₂
    refine hu (fun k => m (σ k)) _ _ (fun τ ε hε => hσ.tendsto_atTop.eventually (hm τ ε hε)) ?_
    have : (fun k => m (σ k)) = fun k t => (m₁ (σ k) t).map (· + ((-((s : ℝ) / 2) : ℝ) : ℂ)) +
        (m₂ (σ k) t).map (· + (((r : ℝ) / 2 : ℝ) : ℂ)) := by
      funext k t
      exact e₃ _ t
    rw [this]
    exact c₃
  refine ⟨⟨⟨p, hp⟩, j₁, j₂⟩, fun k => σ (σ₁ (σ₂ k)), hσ.comp (hσ₁.comp hσ₂), fun τ => ?_, fun w hw => ?_⟩
  · rw [d₃ ⟨⟨p, hp⟩, j₁, j₂⟩ τ, h₀]
    have key : ∀ (n : ℕ) (D' : CD E n) (z : ℝ) (x : (E →+* ℂ) → Multiset ℂ), D'.Inf x →
        ∑ i, ((D'.P i).twist (GlobalTheory.Mem.Chr.CharModel.absChar E (z : ℂ))).infChar τ = (x τ).map (· + (z : ℂ)) := by
      intro n D' z x hx
      rw [← hx τ]
      simp only [fun i => ((hI E _ (D'.P i) (z : ℂ) τ).2)]
      exact (map_sum (Multiset.mapAddMonoidHom (· + (z : ℂ))) _ _).symm
    exact congrArg₂ (· + ·) (key _ _ _ _ v₁) (key _ _ _ _ v₂)
  have := hC.2 (qV E w) r s _ _ _ _ ((GlobalTheory.Mem.Chr.CharModel.absChar E ((-((s : ℝ) / 2) : ℝ) : ℂ)).val w)
    ((GlobalTheory.Mem.Chr.CharModel.absChar E (((r : ℝ) / 2 : ℝ) : ℂ)).val w) (qV_ne_zero w)
    (fun i => (u₁ w hw i).comp hσ₂.tendsto_atTop) (u₂ w hw)
  intro i
  refine (this i).congr fun k => ?_
  exact congrArg (fun M => satEig (qV E w) (r + s) M i) (e₄ _ _ _ (hν _) (hν _) w hw).symm
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula
open GroundTheory.Automorphic.AutomorphicForm (constantTerm)

private theorem readJ_or {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} {bad : Set (UpperTheory.V.Cj.S.Pl E)} {K W m₀}
    {X : Set (CuspSub E N)} {ι : Type} [Fintype ι] {P : ι → Sm E N → Prop} {Q : Sm E N → Prop}
    (h : ∀ i, ReadJ bad K W m₀ X (P i)) (hQ : ∀ φ, IsAutForm φ → Q φ → ∃ i, P i φ) : ReadJ bad K W m₀ X Q := by
  choose J i D C a b using h
  refine ⟨Σ i, J i, inferInstance, fun j => D j.1 j.2, fun j => C j.1 j.2, fun j => a j.1 j.2, fun φ m B h hm => ?_⟩
  choose c hc using fun k => hQ (φ k) (h k).1.aut (h k).2
  obtain ⟨i₀, h0⟩ := Finite.exists_infinite_fiber c
  have h1 : ∃ᶠ k in atTop, c k = i₀ := Nat.frequently_atTop_iff_infinite.2 (Set.infinite_coe_iff.1 h0)
  obtain ⟨σ, hσ, e⟩ := extraction_of_frequently_atTop h1
  obtain ⟨j, s, hs, hI, u⟩ := b i₀ (fun k => φ (σ k)) (fun k => m (σ k)) (fun k => B (σ k)) (fun k => ⟨(h _).1, e k ▸ hc _⟩)
    fun τ ε hε => hσ.tendsto_atTop.eventually (hm τ ε hε)
  exact ⟨⟨i₀, j⟩, fun k => σ (s k), hσ.comp hs, hI, u⟩

private theorem readJ_all (hC : CuspCaseJ) (hT : CtCaseJ) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {bad : Set (UpperTheory.V.Cj.S.Pl E)} (hb : bad.Finite) (N : ℕ) : ∀ K (W : Submodule ℂ (Kinf E N → ℂ)) m₀ (X : Set (CuspSub E N)),
    Lev bad K → FiniteDimensional ℂ W → (∀ π ∈ X, ∀ ψ ∈ π.V, ∀ t g, ψ.1 (splitCentre E N t * g) = ψ.1 g) →
    ReadJ bad K W m₀ X (Excl X) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro K W m₀ X hK hW hX
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨Unit, inferInstance, fun _ => CD.nil E, fun _ _ => 0, fun _ => ⟨fun π _ ⟨i, _⟩ => i.elim0,
      fun w _ => ⟨fun i => i.elim0, fun i => i.elim0, rfl⟩⟩, fun φ m B h hm => ⟨(), id, strictMono_id, ?_, fun w hw i => ?_⟩⟩
    · have e0 : m₀ = fun _ => 0 := by
        funext τ
        obtain ⟨k, hk⟩ := (hm τ 1 one_pos).exists
        have hc := Multiset.card_eq_card_of_rel hk
        rw [((h k).1.cap τ).1] at hc
        exact Multiset.card_eq_zero.1 hc.symm
      rw [e0]
      exact fun _ => rfl
    · have e : ∀ k, B k w = 0 := fun k => Multiset.card_eq_zero.1 ((h k).1.sat w hw).2.2.1
      simp only [e]
      exact tendsto_const_nhds
  have ih' : ∀ M < N, ∀ K (W : Submodule ℂ (Kinf E M → ℂ)) m₀, Lev bad K → FiniteDimensional ℂ W →
      ReadJ (N := M) bad K W m₀ ∅ fun _ => True := fun M hM K W m₀ hK hW =>
    readJ_or (ι := Unit) (fun _ => ih M hM K W m₀ ∅ hK hW fun _ h => h.elim) fun _ _ _ => ⟨(), fun _ h => h.elim⟩
  refine readJ_or (ι := Option {r : Fin N // 0 < r.1})
    (P := fun o φ => o.elim (IsCuspForm φ ∧ Excl X φ) fun r => ∃ g, constantTerm r.1.1 φ.1 g ≠ 0) ?_ fun φ ha hx => ?_
  · rintro (_ | ⟨⟨r, hr⟩, h0⟩)
    · exact hC E N hN bad K W m₀ X hb hK hW hX
    · obtain ⟨s, rfl⟩ : ∃ s, N = r + s := ⟨N - r, by omega⟩
      have h0' : 0 < r := h0
      exact hT E r s h0' (by omega) bad (ih' r hr) (ih' s (by omega)) K W m₀ X hK hW
  · by_cases hc : IsCuspForm φ
    · exact ⟨none, hc, hx⟩
    · have h1 : ¬ GroundTheory.Automorphic.AutomorphicForm.IsCuspidal φ.1 := fun h2 =>
        hc ((UpperTheory.V.Cm.isCuspForm_iff φ).2 ⟨(UpperTheory.V.Cm.isAutForm_iff φ).1 ha, h2⟩)
      unfold GroundTheory.Automorphic.AutomorphicForm.IsCuspidal at h1
      push Not at h1
      obtain ⟨r, h0, hr, hg⟩ := h1
      exact ⟨some ⟨⟨r, hr⟩, h0⟩, hg⟩

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.cuspReadI_of :
    LevShrink → CuspCaseJ → CtCaseJ → CuspReadI := by
  intro hL hC hT E _ _ _ N K W bad m₀ X ho hW hb hl _ hX
  obtain ⟨K', hle, hK', -⟩ := hL E N bad K ho hl
  obtain ⟨J, i, D, C, a, b⟩ := readJ_all hC hT hb N K' W m₀ X hK' hW hX
  classical
  refine ⟨{j : J // (D j).Inf m₀}, inferInstance, fun j => D j.1, fun j => C j.1, fun j => a j.1, fun j => j.2,
    fun φ m B h hm => ?_⟩
  obtain ⟨j, s, hs, hI, u⟩ := b φ m B (fun k =>
    ⟨⟨(h k).1, (h k).2.1, ⟨fun u hu => (h k).2.2.1.1 u (hle hu), (h k).2.2.1.2⟩, (h k).2.2.2.1, (h k).2.2.2.2.1⟩,
      (h k).2.2.2.2.2⟩) hm
  exact ⟨⟨j, hI⟩, s, hs, u⟩
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.regOf :
    MWAt → DualWt → RegOf := by
  intro mw dw E _ _ _ n l D hD τ
  have hτ := hD τ
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · refine ⟨l (InfinitePlace.mk τ), ?_⟩
    have h1 := (mw E n l (InfinitePlace.mk τ)).1
    rw [h] at h1
    rw [hτ, h1]
  · obtain ⟨lam, hlam⟩ := dw n (l (InfinitePlace.mk τ))
    refine ⟨lam, ?_⟩
    have hc : ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding = τ := by
      rw [h]
      ext x
      simp [ComplexEmbedding.conjugate_coe_eq]
    have h2 := (mw E n l (InfinitePlace.mk τ)).2
    rw [hc] at h2
    rw [hτ, h2, hlam]
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem sum_map_eq {ι : Type} [Fintype ι] (f : ι → Multiset ℂ) (g : ℂ → ℂ) :
    ∑ i, (f i).map g = (∑ i, f i).map g :=
  (map_sum (Multiset.mapAddMonoidHom g) f Finset.univ).symm

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.twDataT :
    CDAddG → MuInf → MWAt → DualWt → TwDataT := by
  intro hAdd hMu hMW hDW E _ _ _ n a b hab ha hb μ e hμ l₁ l₂ lam hlam D₁ D₂ h₁ h₂
  subst hab
  obtain ⟨D, hnot, hsat, hinf⟩ := hAdd E a b D₁ D₂ (μ ^ b) (μ ^ a) ha hb
  have hval : ∀ (w : Pl E) (k : ℕ), (μ ^ k).val w = μ.val w ^ k :=
    fun w k => MonoidHom.pow_apply μ.1 k _
  have hunr : ∀ {w : Pl E} (k : ℕ), μ.UnrAt w → (μ ^ k).UnrAt w := by
    intro w k h x hx
    have e1 : (μ ^ k).loc w x = μ.loc w x ^ k := MonoidHom.pow_apply μ.1 k _
    rw [e1, h x hx, one_pow]
  have hT := (hMu E μ e hμ).2
  have hemb : ∀ {m : ℕ} (C : CD E m) (l : InfinitePlace E → DomWeight m) (k : ℕ), C.Inf (mW l) →
      ∀ v : InfinitePlace E, ∑ i, ((C.P i).twist (μ ^ k)).infChar v.embedding =
        (infOfWeight (l v)).map (· + (k : ℂ) * (e v : ℂ) / 2) := by
    intro m C l k hC v
    have h1 : ∀ i, ((C.P i).twist (μ ^ k)).infChar v.embedding =
        ((C.P i).infChar v.embedding).map (· + (k : ℂ) * (e v : ℂ) / 2) :=
      fun i => (hT (C.N i) k (C.P i) v).1
    simp only [h1]
    rw [sum_map_eq, hC v.embedding, (hMW E m l v).1]
  have hcon : ∀ {m : ℕ} (C : CD E m) (l : InfinitePlace E → DomWeight m) (k : ℕ), C.Inf (mW l) →
      ∀ v : InfinitePlace E, ∑ i, ((C.P i).twist (μ ^ k)).infChar (ComplexEmbedding.conjugate v.embedding) =
        (infOfWeight (l v)).map (fun t => -(t + (k : ℂ) * (e v : ℂ) / 2)) := by
    intro m C l k hC v
    have h1 : ∀ i, ((C.P i).twist (μ ^ k)).infChar (ComplexEmbedding.conjugate v.embedding) =
        ((C.P i).infChar (ComplexEmbedding.conjugate v.embedding)).map (· - (k : ℂ) * (e v : ℂ) / 2) :=
      fun i => (hT (C.N i) k (C.P i) v).2
    simp only [h1]
    rw [sum_map_eq, hC (ComplexEmbedding.conjugate v.embedding), (hMW E m l v).2, Multiset.map_map]
    refine Multiset.map_congr rfl fun t _ => ?_
    simp only [Function.comp_apply]
    ring
  refine ⟨D, hnot, ?_, ?_⟩
  · intro τ
    rcases InfinitePlace.embedding_mk_eq τ with h | h
    · refine ⟨lam (InfinitePlace.mk τ), ?_⟩
      rw [hinf τ, ← hlam (InfinitePlace.mk τ), ← hemb D₁ l₁ b h₁, ← hemb D₂ l₂ a h₂, h]
    · obtain ⟨lam', hl⟩ := hDW (a + b) (lam (InfinitePlace.mk τ))
      have hτ : τ = ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding := by
        rw [h]
        exact (star_star τ).symm
      refine ⟨lam', ?_⟩
      rw [hinf τ, hl, ← hlam (InfinitePlace.mk τ), Multiset.map_add, Multiset.map_map, Multiset.map_map]
      have e1 := hcon D₁ l₁ b h₁ (InfinitePlace.mk τ)
      have e2 := hcon D₂ l₂ a h₂ (InfinitePlace.mk τ)
      rw [← hτ] at e1 e2
      rw [e1, e2]
      rfl
  · intro w B₁ B₂ hu s₁ s₂
    have h := hsat w B₁ B₂ (hunr b hu) (hunr a hu) s₁ s₂
    rw [hval, hval] at h
    exact h
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem inv_map_sign (B : Multiset ℂˣ) (k : ℕ) (h : inv B = B) :
    inv (B.map (· * (-1 : ℂˣ) ^ k)) = B.map (· * (-1 : ℂˣ) ^ k) := by
  have hk : ((-1 : ℂˣ) ^ k)⁻¹ = (-1 : ℂˣ) ^ k := by
    rw [← inv_pow, inv_neg_one]
  conv_rhs => rw [← h]
  simp only [UpperTheory.V.Z.Tf.GlobalTraceComparison.inv, Multiset.map_map]
  refine Multiset.map_congr rfl fun x _ => ?_
  simp only [Function.comp_apply, mul_inv, hk]

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.unStable :
    UnStable := by
  intro E _ _ _ μ a b w B₁ B₂ hμ h₁ h₂
  have hadd : ∀ X Y : Multiset ℂˣ, inv (X + Y) = inv X + inv Y := fun X Y => Multiset.map_add _ _ _
  simp only [un, hμ]
  rw [hadd, inv_map_sign B₁ b h₁, inv_map_sign B₂ a h₂]
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.csdInert :
    GOne.CsdSat → CsdInert := by
  intro h E _ _ _ n hn π hd
  filter_upwards [h E n hn π hd] with w hw hns B hB
  obtain ⟨B₀, hB₀, hc⟩ := hw
  obtain rfl := CG.HasSat.unique hB hB₀
  exact CG.HasSat.unique (hc w ⟨rfl, Or.inr hns⟩) hB
end

section
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm PositivityTheory.Rg.BcB.G8

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem cuspReadI : CuspReadI :=
  cuspReadI_of levShrink (cuspCaseJ cuspMem cuspFin normTw normUniq satComb absInf mtoLaws)
    (ctCaseJ (stepT (iwaT levShrink typeSat) sliceT stabT) splitLim satComb cdAddG absInf mtoLaws)

theorem asmTh : AsmTh :=
  asmTh_of (rChoice places levelFn regFn) (fun h => rUEval h places exAct splitLine inertLine uConj)
    (fun h1 h3 => rFamMatch h1 h3 places exAct exHecke2 ctEx muConj) ends (twDataT cdAddG muInf mwAt dualWt) (regOf mwAt dualWt)
    unStable muInf (csdInert GOne.csdSat) (rSep places) regCt trAvg places

theorem runTh_of (hU : GlobalTheory.BCT.USide) (hG : G2s) (hM : MuEx) (h1 : MatchUnit) (h3 : MatchSplit) (hS : StUnit) (hE : EndoBlockG)
    (hB : StableBlockG) : RunTh :=
  asmTh hU hG hM h1 h3 (endoS (enlarge hS hecke_eigenvalues_unitary_one_factor unitary_one_characters_separated_by_eigenvalues places) places hE) (stableS (enlarge hS hecke_eigenvalues_unitary_one_factor unitary_one_characters_separated_by_eigenvalues places) places hB)

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula
end
