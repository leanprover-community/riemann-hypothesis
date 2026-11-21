import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricShiftOfIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFamilyMovingPartsChainBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionIffLocalQuotients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionTensorIsometricTransShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsArithVarEffCartier
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GenericOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalModelRegularUnitValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeNonnegOfSemiPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBallFamMonoNegAdd
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.FsTop

variable {X : Scheme.{0}} [IsIntegral X]

theorem regAt_mul' {x : X} {a b : X.functionField} (ha : RegAt x a) (hb : RegAt x b) : RegAt x (a * b) := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  exact ⟨u * v, map_mul _ u v⟩

theorem regAt_inv_of_unitAt {x : X} {a : X.functionField} (ha : UnitAt x a) : RegAt x a⁻¹ := by
  obtain ⟨u, hu, rfl⟩ := ha
  refine ⟨(hu.unit⁻¹ : (X.presheaf.stalk x)ˣ), ?_⟩
  refine (eq_inv_of_mul_eq_one_left ?_)
  rw [← map_mul]
  simp

end GlobalTheory.HSNef.FsTop

open GlobalTheory.HSNef.FsTop in

theorem GlobalTheory.HSNef.le_shift_of_isFS : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M B : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → SmallFam B f w → Le M (B.shift (fun _ => Real.log (Fintype.card J) / 2) fun _ => rfl) := by
  intro k _ X _ p M B J _ f w hM hB
  obtain ⟨ρ, hρ, hreg, hφ⟩ := hM
  obtain ⟨β, hβ, hbreg, hbnorm⟩ := hB
  have key : ∀ (x : X) (c : B.B.ι) (d : M.B.ι), x ∈ B.B.U c → x ∈ M.B.U d →
      RegAt x ((β c : X.functionField) / (ρ d : X.functionField)) := by
    intro x c d hc hd
    obtain ⟨l, hl⟩ := (hreg x d hd).2
    have hfl : f l ≠ 0 := fun h => hl.ne_zero (by rw [h, zero_mul])
    have e : (β c : X.functionField) / (ρ d) = (f l * β c) * (f l * ρ d)⁻¹ := by
      field_simp
    rw [e]
    exact regAt_mul' (hbreg x c hc l) (regAt_inv_of_unitAt hl)
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p _ M).2 ⟨β, ρ, hβ, hρ, fun x i j hi hj => key x i j hi hj, ?_⟩
  intro σ y i j hi hj
  have hxi : under y ∈ B.B.U i := mem_ptsIn.1 hi
  have hxj : under y ∈ M.B.U j := mem_ptsIn.1 hj
  have hq := key _ i j hxi hxj
  obtain ⟨l₀, hl₀⟩ := (hreg _ j hxj).2
  set q : X.functionField := (β i : X.functionField) / (ρ j : X.functionField) with hqdef
  have hval : ∀ l, ratVal (f l * (β i : X.functionField)) y = ratVal q y * ratVal (f l * (ρ j : X.functionField)) y := by
    intro l
    have e : f l * (β i : X.functionField) = q * (f l * (ρ j : X.functionField)) := by
      rw [hqdef]; field_simp
    rw [e, ratVal_mul hq ((hreg _ j hxj).1 l)]
  have hφj : (M.φ σ).φ j y = Real.log (∑ l, ‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l)) :=
    hφ σ y j hj
  have hφi : ((B.shift (fun _ => Real.log (Fintype.card J) / 2) fun _ => rfl).φ σ).φ i y =
      (B.φ σ).φ i y + 2 * (Real.log (Fintype.card J) / 2) := rfl
  set S := ∑ l, ‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l) with hS
  set φB := (B.φ σ).φ i y
  set Q := ‖ratVal q y‖
  have hn : (1 : ℝ) ≤ Fintype.card J := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨l₀⟩
  have hSpos : 0 < S := by
    have h0 : 0 < ‖ratVal (f l₀ * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l₀) :=
      mul_pos (pow_pos (norm_pos_iff.2 (ratVal_ne_zero hl₀)) 2) (Real.exp_pos _)
    exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun l => ‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l))
      (fun l _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (Finset.mem_univ l₀))

  have hterm : ∀ l, Q ^ 2 * (‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l)) ≤ Real.exp φB := by
    intro l
    have h1 := hbnorm σ y i hi l
    rw [hval l, norm_mul] at h1
    have h2 : Q * ‖ratVal (f l * (ρ j : X.functionField)) y‖ ≤ Real.exp (-w l) * Real.exp (φB / 2) := by
      have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (φB / 2)).le
      rwa [mul_assoc, ← Real.exp_add, show -φB / 2 + φB / 2 = 0 by ring, Real.exp_zero, mul_one] at this
    have h3 := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h2 2
    have e1 : (Real.exp (-w l) * Real.exp (φB / 2)) ^ 2 * Real.exp (2 * w l) = Real.exp φB := by
      rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1; push_cast; ring
    calc Q ^ 2 * (‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l))
        = (Q * ‖ratVal (f l * (ρ j : X.functionField)) y‖) ^ 2 * Real.exp (2 * w l) := by ring
      _ ≤ (Real.exp (-w l) * Real.exp (φB / 2)) ^ 2 * Real.exp (2 * w l) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = Real.exp φB := e1
  have hsum : Q ^ 2 * S ≤ Fintype.card J * Real.exp φB := by
    rw [hS, Finset.mul_sum]
    calc ∑ l, Q ^ 2 * (‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l))
        ≤ ∑ _l : J, Real.exp φB := Finset.sum_le_sum fun l _ => hterm l
      _ = Fintype.card J * Real.exp φB := by simp
  rw [hφi, hφj]
  have hE : Real.exp (-(φB + 2 * (Real.log (Fintype.card J) / 2) - Real.log S) / 2) ^ 2 =
      S / (Fintype.card J * Real.exp φB) := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-(φB + 2 * (Real.log (Fintype.card J) / 2) - Real.log S) / 2)
        = Real.log S - (Real.log (Fintype.card J) + φB) by push_cast; ring,
      Real.exp_sub, Real.exp_add, Real.exp_log hSpos, Real.exp_log (by linarith)]
  have hpos : 0 ≤ Q * Real.exp (-(φB + 2 * (Real.log (Fintype.card J) / 2) - Real.log S) / 2) :=
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine (pow_le_one_iff_of_nonneg hpos two_ne_zero).1 ?_
  rw [mul_pow, hE, ← mul_div_assoc, div_le_one (by positivity)]
  exact hsum
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubiniStudy_le_shift_of_smallSections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M B : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → SmallFam B f w → Le M (B.shift (fun _ => Real.log (Fintype.card J) / 2) fun _ => rfl) := by
  atlas_forward_decl GlobalTheory.HSNef.le_shift_of_isFS
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem isometric_pull_shiftC {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    (L : HermLB p) (t : ℝ) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    ((L.shift (fun _ => t) fun _ => rfl).pull π hπ).Isometric ((L.pull π hπ).shift (fun _ => t) fun _ => rfl) :=
  HermLB.isometric_of_eqOn fun σ a y _ => by
    exact (congrArg (· + 2 * t) (Weight.pull_φ (L.φ σ) π hπ a y)).trans
      (Weight.pull_φ ((L.φ σ).addFn fun _ => 2 * t) π hπ a y).symm

theorem gdeg_pull_model : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q)
    (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ L : HermLB p, gdeg (L.pull π hπ) D = gdeg L D ∧
    ∀ (a t : ℝ), L.IsSelfInter a →
      ((L.pull π hπ).shift (fun _ => t) fun _ => rfl).IsSelfInter (a + ((D : ℝ) + 1) * t * gdeg L D) := by
  intro hC k _ X Y _ _ p q D hX hY π hπ φ hM L
  have hdeg : π.residueDegree (genericPoint Y) ≠ 0 := by rw [hM.deg]; exact one_ne_zero
  have hP := ((hC.arProj k X Y p q D hX hY π hπ hM.gen hdeg).1)
  have hP1 : ∀ (M : HermLB p) (a : ℝ), M.IsSelfInter a → (M.pull π hπ).IsSelfInter a := fun M a h => by
    have := hP M a h
    rwa [hM.deg, Nat.cast_one, one_mul] at this
  have hS := hC.arShift
  have hg : gdeg (L.pull π hπ) D = gdeg L D := by
    obtain ⟨h, hh⟩ := ((hC.arExists k X p D hX).1 L)
    have ha : L.IsSelfInter (h (genericPoint X)) := ⟨h, hh, rfl⟩
    set a := h (genericPoint X)

    have h1 := hP1 _ _ (hS k X p D hX L a 1 ha)
    have h1' := (isometric_pull_shiftC L 1 π hπ).isSelfInter hY h1
    have h2 := hS k Y q D hY (L.pull π hπ) a 1 (hP1 L a ha)
    have e := HermLB.IsSelfInter.unique hY h1' h2
    have hD : ((D : ℝ) + 1) ≠ 0 := by positivity
    have : ((D : ℝ) + 1) * gdeg L D = ((D : ℝ) + 1) * gdeg (L.pull π hπ) D := by linarith
    exact (mul_left_cancel₀ hD this).symm
  refine ⟨hg, fun a t ha => ?_⟩
  have := hS k Y q D hY (L.pull π hπ) a t (hP1 L a ha)
  rwa [hg] at this

end GlobalTheory.HSNef
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricDegree_pull_birationalModel : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ L : HermLB p, gdeg (L.pull π hπ) D = gdeg L D ∧ ∀ (a t : ℝ), L.IsSelfInter a → ((L.pull π hπ).shift (fun _ => t) fun _ => rfl).IsSelfInter (a + ((D : ℝ) + 1) * t * gdeg L D) := by
  atlas_forward_decl GlobalTheory.HSNef.gdeg_pull_model
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem isModel_id (X : Scheme.{0}) [IsIntegral X] : IsModel (𝟙 X) (RingHom.id X.functionField) where
  gen := rfl
  deg := Scheme.Hom.residueDegree_id _
  compat y a := by
    simp only [RingHom.id_apply, Scheme.Hom.stalkMap_id]
    rfl

theorem IsModel.comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z] {π : Y ⟶ X} {π' : Z ⟶ Y}
    {φ : X.functionField →+* Y.functionField} {φ' : Y.functionField →+* Z.functionField}
    (h : IsModel π φ) (h' : IsModel π' φ') : IsModel (π' ≫ π) (φ'.comp φ) where
  gen := by
    show π (π' (genericPoint Z)) = genericPoint X
    rw [h'.gen, h.gen]
  deg := by
    rw [GlobalTheory.CurveDegreesCompare.residueDegree_comp π' π (genericPoint Z), h'.deg]
    rw [h'.gen, h.deg]
  compat z a := by
    refine (congrArg φ' (h.compat (π' z) a)).trans ((h'.compat z _).trans ?_)
    rw [Scheme.Hom.stalkMap_comp]
    rfl

theorem isModel_id_and_comp : ∀ (X Y Z : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (π : Y ⟶ X) (π' : Z ⟶ Y)
    (φ : X.functionField →+* Y.functionField) (φ' : Y.functionField →+* Z.functionField),
    IsModel (𝟙 X) (RingHom.id _) ∧ (IsModel π φ → IsModel π' φ' → IsModel (π' ≫ π) (φ'.comp φ)) :=
  fun X _ _ _ _ _ _ _ _ _ => ⟨isModel_id X, fun h h' => h.comp h'⟩

end GlobalTheory.HSNef
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBirationalModel_id_and_comp : ∀ (X Y Z : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (π : Y ⟶ X) (π' : Z ⟶ Y) (φ : X.functionField →+* Y.functionField) (φ' : Y.functionField →+* Z.functionField), IsModel (𝟙 X) (RingHom.id _) ∧ (IsModel π φ → IsModel π' φ' → IsModel (π' ≫ π) (φ'.comp φ)) := by
  atlas_forward_decl GlobalTheory.HSNef.isModel_id_and_comp
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

namespace GlobalTheory.BlowArith

theorem exists_isArithVar_effCartier_isIso (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X] (D : ℕ) (hX : IsArithVar p D) (J : X.IdealSheafData)
    (hJ : genericPoint X ∉ J.support) :
    ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X), IsArithVar (ρ ≫ p) D ∧
      ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap ρ) ∧
      ∀ V : X.Opens, (∀ x ∈ V, x ∉ J.support) → IsIso (ρ ∣_ V) := by
  have := hX.isNoetherianRing
  obtain ⟨Y, b, hb, hproj, hiso⟩ := ProjBlowup.exists_blowup p hX.isProjOver J
  let V : X.Opens := J.support.compl
  have hbV : IsIso (b ∣_ V) := hiso V fun _ hx => hx
  have : Nonempty V.toScheme := ⟨⟨genericPoint X, hJ⟩⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : Nonempty (b ⁻¹ᵁ V).toScheme := ⟨inv (b ∣_ V) (Classical.arbitrary _)⟩
  have : IsIntegral (b ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (b ∣_ V)
  have hU : (J.comap b).support.compl = b ⁻¹ᵁ V := by
    ext y
    exact not_congr (ProjBlowup.mem_support_comap J b y)
  have hdom : IsSchemeTheoreticallyDominant (b ⁻¹ᵁ V).ι :=
    hU ▸ ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier Y _ hb.1
  have : IsNoetherian Y := isNoetherian_of_isProjOver hproj
  have : IsIntegral Y := by
    have : IsReduced Y := IsSchemeTheoreticallyDominant.isReduced (b ⁻¹ᵁ V).ι
    have h := ((IrreducibleSpace.isIrreducible_univ (b ⁻¹ᵁ V).toScheme).image _
      (b ⁻¹ᵁ V).ι.continuous.continuousOn).closure
    rw [Set.image_univ, (b ⁻¹ᵁ V).ι.denseRange.closure_range] at h
    have : IrreducibleSpace Y := (irreducibleSpace_def _).2 h
    exact isIntegral_of_irreducibleSpace_of_isReduced Y
  have hfac : (b ⁻¹ᵁ V).ι ≫ b = b ∣_ V ≫ V.ι := (morphismRestrict_ι b V).symm
  have hoi : IsOpenImmersion ((b ⁻¹ᵁ V).ι ≫ b) := by rw [hfac]; infer_instance
  have hg : (b ⁻¹ᵁ V).ι (genericPoint _) = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have hgen : b (genericPoint Y) = genericPoint X := by
    rw [← hg, ← Scheme.Hom.comp_apply]
    exact genericPoint_eq_of_isOpenImmersion _
  have hdeg : b.residueDegree (genericPoint Y) ≠ 0 := by
    intro h0
    have h1 := CurveDegreesCompare.residueDegree_comp (b ⁻¹ᵁ V).ι b (genericPoint _)
    rw [CurveDegreesCompare.residueDegree_of_isOpenImmersion, hg, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hflat : Flat ((b ≫ p) ≫ spMap (Int.castRingHom k)) := by
    rw [flat_int_iff_charZero]
    have := hX.charZero
    have : IsDominant b := ⟨by
      rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← genericPoint_closure]
      exact closure_mono (Set.singleton_subset_iff.2 ⟨_, hgen⟩)⟩
    have := IsSchemeTheoreticallyDominant.of_isDominant b
    have hinj' : Function.Injective b.appTop := Scheme.Hom.app_injective b ⊤
    exact charZero_of_injective_ringHom (f := b.appTop.hom) hinj'
  exact ⟨Y, b, ⟨hX.isDomain, hX.finite, ‹_›, hproj, hflat,
    DimCover.topologicalKrullDim_eq k X Y p (b ≫ p) D hX hproj hflat b rfl hgen hdeg⟩, hb.1, hiso⟩

end GlobalTheory.BlowArith

namespace GlobalTheory.ArLieBase

theorem exists_blowup_principalises : ∀ (F : Type) [Field F] [NumberField F] (G T : Scheme.{0}) (s : G ⟶ Sp F) (S : Set G) (d : ℕ) (ι : G ⟶ T) (X W : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (jB : W ⟶ X) (πB : W ⟶ G) (ρ : X ⟶ T), IsPre s S d ι q jB πB ρ → ∀ (n : ℕ) (U : Fin n → X.Opens) (m : Fin n → ℕ) (A : ∀ j, Fin (m j) → Γ(X, U j)) (N : Fin n → ℕ), (∀ j, IsAffineOpen (U j)) → (∀ j, N j ≠ 0) → (∀ j, (N j : Γ(X, U j)) ∈ (Ideal.span (Set.range (A j))).radical) → ∃ (X' W' : Scheme.{0}) (b : X' ⟶ X) (jB' : W' ⟶ X') (πB' : W' ⟶ G), IsPre s S d ι (b ≫ q) jB' πB' (b ≫ ρ) ∧ ∀ (Y : Scheme.{0}) (ν : Y ⟶ X') (w : Y) (j : Fin n), (ν ≫ b) w ∈ U j → ∃ (V : Y.Opens) (hV : V ≤ (ν ≫ b) ⁻¹ᵁ U j), w ∈ V ∧ IsAffineOpen V ∧ ∃ k, ∀ k', ((ν ≫ b).appLE (U j) V hV).hom (A j k) ∣ ((ν ≫ b).appLE (U j) V hV).hom (A j k') := by
  intro F _ _ G T s S d ι X W q jB πB ρ h n U m A N hU hN hA
  have hX := h.1
  have := hX.isIntegral
  have := hX.isLocallyNoetherian
  have hc := hX.charZero
  set p : ℕ := ∏ j, N j with hpdef
  have hp0 : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hN j
  have hpA : ∀ j, (p : Γ(X, U j)) ∈ (Ideal.span (Set.range (A j))).radical := by
    intro j
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ j)
    rw [hpdef, hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hA j)
  obtain ⟨J, hJp, hJE⟩ := GlobalTheory.Principalise.exists_idealSheaf_principalises X p n U m A hU hpA
  have hgen : genericPoint X ∈ X.basicOpen (p : Γ(X, ⊤)) := by
    have hne : (p : Γ(X, ⊤)) ≠ 0 := Nat.cast_ne_zero.2 hp0
    have hb : X.basicOpen (p : Γ(X, ⊤)) ≠ ⊥ := fun h0 => hne ((basicOpen_eq_bot_iff _).1 h0)
    have : Nonempty (X.basicOpen (p : Γ(X, ⊤))) := by
      by_contra h1
      apply hb
      rw [eq_bot_iff]
      intro x hx
      exact (h1 ⟨⟨x, hx⟩⟩).elim
    exact ((genericPoint_spec X).mem_open_set_iff (X.basicOpen (p : Γ(X, ⊤))).isOpen).mpr
      (by simpa using this)
  have hJg : genericPoint X ∉ J.support := fun hx => hJp _ hx hgen
  obtain ⟨X', b, hX', hE, hiso⟩ := GlobalTheory.BlowArith.exists_isArithVar_effCartier_isIso (𝓞 F) X q d hX J hJg
  let V : X.Opens := J.support.compl
  have hbV : IsIso (b ∣_ V) := hiso V fun _ hx => hx
  have huF : IsUnit ((p : ℕ) : Γ(Sp F, ⊤)) := by
    have := (IsUnit.mk0 (p : F) (Nat.cast_ne_zero.2 hp0)).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    simpa using this
  have huW : IsUnit ((p : ℕ) : Γ(W, ⊤)) := by
    let φ : Γ(Sp F, ⊤) →+* Γ(W, ⊤) := ((πB ≫ s).app ⊤).hom
    have := huF.map φ
    rwa [map_natCast φ] at this
  have hrange : Set.range jB ⊆ Set.range V.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hw : w ∈ jB ⁻¹ᵁ X.basicOpen (p : Γ(X, ⊤)) := by
      simp only [Scheme.preimage_basicOpen, map_natCast]
      exact (Scheme.basicOpen_of_isUnit W huW).ge (show w ∈ (⊤ : W.Opens) from trivial)
    exact fun hx => hJp _ hx hw
  let jV : W ⟶ V.toScheme := IsOpenImmersion.lift V.ι jB hrange
  have hjV : jV ≫ V.ι = jB := IsOpenImmersion.lift_fac _ _ _
  let jB' : W ⟶ X' := jV ≫ inv (b ∣_ V) ≫ (b ⁻¹ᵁ V).ι
  have hjB' : jB' ≫ b = jB := by
    simp only [jB', Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, hjV]
  have hsq : IsPullback jB' (𝟙 W) b jB := by
    have h1 : IsPullback (jV ≫ inv (b ∣_ V)) (𝟙 W) (b ∣_ V) jV :=
      IsPullback.of_vert_isIso ⟨by simp⟩
    have h2 := h1.paste_horiz (isPullback_morphismRestrict b V).flip
    simpa [jB', Category.assoc, hjV] using h2
  have hpb : IsPullback jB' (πB ≫ s) (b ≫ q) (spMap (algebraMap (𝓞 F) F)) := by
    simpa using hsq.paste_vert h.2.1
  refine ⟨X', W, b, jB', πB, ⟨hX', hpb, h.2.2.1, h.2.2.2.1, ?_⟩, ?_⟩
  · rw [← Category.assoc, hjB']
    exact h.2.2.2.2
  · intro Y ν w j hw
    exact hJE X' Y b ν hE w j hw

end GlobalTheory.ArLieBase
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem isModel_of_isIso_restrict : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) (U : X.Opens),
    (U : Set X).Nonempty → IsIso (π ∣_ U) → ∃ φ : X.functionField →+* Y.functionField, IsModel π φ := by
  intro X Y _ _ π U hU hiso
  obtain ⟨h₁, h₂⟩ := GlobalTheory.Published.generic_of_isIso_restrict π U hU
  have e : closure ({genericPoint X} : Set X) = Set.univ := (genericPoint_spec X).def
  have hd : IsDominant π := ⟨dense_iff_closure_eq.mpr
    (Set.eq_univ_of_univ_subset (e ▸ closure_mono (Set.singleton_subset_iff.mpr ⟨_, h₁⟩)))⟩
  exact ⟨functionFieldMap π, h₁, h₂, fun y a => functionFieldMap_algebraMap π y a⟩

end GlobalTheory.HSNef
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBirationalModel_of_isIso_over_nonempty_open : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) (U : X.Opens), (U : Set X).Nonempty → IsIso (π ∣_ U) → ∃ φ : X.functionField →+* Y.functionField, IsModel π φ := by
  atlas_forward_decl GlobalTheory.HSNef.isModel_of_isIso_restrict
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.RegOrInvModel

theorem exists_idealSheaf_principalises_of_ne_zero : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (n : ℕ) (U : Fin n → X.Opens) (m : Fin n → ℕ) (A : ∀ j, Fin (m j) → Γ(X, U j)), (∀ j, IsAffineOpen (U j)) → (∀ j, ∃ k, A j k ≠ 0) → ∃ J : X.IdealSheafData, genericPoint X ∉ J.support ∧ ∀ (W : Scheme.{0}) (b : W ⟶ X), ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap b) → ∀ (w : W) (j : Fin n), b w ∈ U j → ∃ (V : W.Opens) (hV : V ≤ b ⁻¹ᵁ U j), w ∈ V ∧ IsAffineOpen V ∧ ∃ k, ∀ k', (b.appLE (U j) V hV).hom (A j k) ∣ (b.appLE (U j) V hV).hom (A j k') := by
  intro X _ _ n U m A hU hA
  choose J hJU hJp using fun j => GlobalTheory.Principalise.kerIdealAffine X (U j) (hU j) (Ideal.span (Set.range (A j)))
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hηV₀, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have hsupp : ∀ I : X.IdealSheafData, genericPoint X ∉ I.support ↔
      ∃ f ∈ I.ideal ⟨V₀, hV₀⟩, genericPoint X ∈ X.basicOpen f := by
    intro I
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V₀, hV₀⟩) hηV₀, Scheme.mem_zeroLocus_iff]
    push_neg
    rfl
  have hmul : ∀ I I' : X.IdealSheafData, genericPoint X ∉ I.support → genericPoint X ∉ I'.support →
      genericPoint X ∉ (I * I').support := by
    intro I I' h h'
    obtain ⟨f, hf, hηf⟩ := (hsupp I).1 h
    obtain ⟨f', hf', hηf'⟩ := (hsupp I').1 h'
    refine (hsupp _).2 ⟨f * f', ?_, ?_⟩
    · rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
      exact Ideal.mul_mem_mul hf hf'
    · rw [Scheme.basicOpen_mul]
      exact ⟨hηf, hηf'⟩
  have hone : genericPoint X ∉ (1 : X.IdealSheafData).support := by
    refine (hsupp _).2 ⟨1, ?_, ?_⟩
    · show (1 : Γ(X, V₀)) ∈ (⊤ : X.IdealSheafData).ideal ⟨V₀, hV₀⟩
      rw [Scheme.IdealSheafData.ideal_top]
      exact Submodule.mem_top
    · rw [Scheme.basicOpen_one]
      exact hηV₀
  have hJj : ∀ j, genericPoint X ∉ (J j).support := by
    intro j
    obtain ⟨k, hk⟩ := hA j
    have hb : X.basicOpen (A j k) ≠ ⊥ := fun h0 => hk ((basicOpen_eq_bot_iff _).1 h0)
    obtain ⟨x, hx⟩ : ∃ x, x ∈ X.basicOpen (A j k) := by
      by_contra hc
      push_neg at hc
      exact hb (eq_bot_iff.2 fun x hx => (hc x hx).elim)
    have hηb : genericPoint X ∈ X.basicOpen (A j k) := gen_mem hx
    have hηU : genericPoint X ∈ U j := X.basicOpen_le _ hηb
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U j, hU j⟩) hηU, Scheme.mem_zeroLocus_iff, hJU j]
    exact fun h => h _ (Ideal.subset_span ⟨k, rfl⟩) hηb
  refine ⟨∏ j, J j, ?_, ?_⟩
  · exact Finset.prod_induction J (fun I => genericPoint X ∉ I.support) hmul hone fun j _ => hJj j
  · intro W b hE w j hw
    obtain ⟨V₁, f, hw₁, hf, hV₁⟩ := hE w
    obtain ⟨g, hgle, hwg⟩ := V₁.2.exists_basicOpen_le (V := V₁.1 ⊓ b ⁻¹ᵁ U j) ⟨w, hw₁, hw⟩ hw₁
    have hDU : (W.affineBasicOpen g).1 ≤ b ⁻¹ᵁ U j := hgle.trans inf_le_right
    have hDV : (W.affineBasicOpen g).1 ≤ V₁.1 := W.basicOpen_le g
    have hfD : (W.presheaf.map (homOfLE hDV).op).hom f ∈ nonZeroDivisors Γ(W, (W.affineBasicOpen g).1) :=
      (GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen (W.affineBasicOpen g).2).1
        (((GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen V₁.2).2 hf).resG hDV)
    have hI1 := ((∏ i, J i).comap b).map_ideal_basicOpen V₁ g
    rw [hV₁, Ideal.map_span, Set.image_singleton] at hI1
    have hI2 := GlobalTheory.Principalise.comapIdealAffine (∏ i, J i) b ⟨U j, hU j⟩ (W.affineBasicOpen g) hDU
    rw [← Finset.mul_prod_erase Finset.univ J (Finset.mem_univ j), Scheme.IdealSheafData.ideal_mul,
      Pi.mul_apply, Ideal.map_mul, hJU, Ideal.map_span, ← Set.range_comp] at hI2
    rw [← Finset.mul_prod_erase Finset.univ J (Finset.mem_univ j)] at hI1
    have hwD : w ∈ (W.affineBasicOpen g).1 := hwg
    obtain ⟨k, s, hsP, hdiv⟩ := GlobalTheory.Principalise.exists_dvd_of_span_mul_eq
      (Ideal.comap (W.presheaf.germ (W.affineBasicOpen g).1 w hwD).hom (IsLocalRing.maximalIdeal _)) _ _
      (hI2.symm.trans hI1.symm) hfD
    have hsu : w ∈ W.basicOpen s := by
      rw [Scheme.mem_basicOpen _ _ _ hwD]
      by_contra hc
      exact hsP ((IsLocalRing.mem_maximalIdeal _).2 hc)
    have hED : W.basicOpen s ≤ (W.affineBasicOpen g).1 := W.basicOpen_le s
    have hV : W.basicOpen s ≤ b ⁻¹ᵁ U j := fun x hx => hDU (hED hx)
    refine ⟨W.basicOpen s, hV, hsu, (W.affineBasicOpen g).2.basicOpen s, k, fun k' => ?_⟩
    have key : b.appLE (U j) _ hDU ≫ W.presheaf.map (homOfLE hED).op = b.appLE (U j) (W.basicOpen s) hV :=
      Scheme.Hom.appLE_map _ _ _
    have hu := W.toRingedSpace.isUnit_res_basicOpen s
    have h1 := map_dvd (W.presheaf.map (homOfLE hED).op).hom (hdiv k')
    rw [map_mul] at h1
    have h2 := hu.dvd_mul_left.1 h1
    rw [← key]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    exact h2

theorem exists_model_regAt_or_regAt_inv : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ g : X.functionField, g ≠ 0 → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField), IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ ∀ y : Y, RegAt y (φ g) ∨ RegAt y (φ g)⁻¹ := by
  intro k _ X _ p D hX g hg
  have := hX.isLocallyNoetherian
  have := hX.isNoetherian
  choose V hVa hxV using fun x : X => (by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨V, hV, hx⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  let e := t.equivFin
  let U : Fin t.card → X.Opens := fun j => V (e.symm j).1
  have hU : ∀ j, IsAffineOpen (U j) := fun j => hVa _
  have hη : ∀ j, genericPoint X ∈ U j := fun j => gen_mem (hxV (e.symm j).1)
  have hfr : ∀ j, ∃ a b : Γ(X, U j), b ≠ 0 ∧ fnOf (U j) (hη j) a / fnOf (U j) (hη j) b = g := by
    intro j
    have : Nonempty (U j) := ⟨⟨_, hη j⟩⟩
    have := functionField_isFractionRing_of_isAffineOpen X (U j) (hU j)
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, U j)) g
    exact ⟨a, b, nonZeroDivisors.ne_zero hb, hab⟩
  choose a b hb hab using hfr
  let A : ∀ j, Fin 2 → Γ(X, U j) := fun j => ![a j, b j]
  obtain ⟨J, hJη, hJdiv⟩ := exists_idealSheaf_principalises_of_ne_zero X t.card U (fun _ => 2) A hU fun j => ⟨1, hb j⟩
  obtain ⟨Y, ρ, hY, hE, hiso⟩ := GlobalTheory.BlowArith.exists_isArithVar_effCartier_isIso k X p D hX J hJη
  have : IsIntegral Y := hY.isIntegral
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.isBirationalModel_of_isIso_over_nonempty_open X Y ρ J.support.compl ⟨genericPoint X, hJη⟩ (hiso _ fun _ hx => hx)
  obtain ⟨-, -, hfn, -⟩ := GlobalTheory.T.birationalModel_regular_unit_values k X Y p (ρ ≫ p) ρ rfl φ hφ
  refine ⟨Y, inferInstance, ρ, φ, hY, hφ, fun y => ?_⟩
  obtain ⟨x, hxt, hyx⟩ : ∃ x ∈ t, ρ y ∈ V x := by
    simpa using ht (Set.mem_univ (ρ y))
  set j := e ⟨x, hxt⟩ with hj
  have hyj : ρ y ∈ U j := by simpa [U, j] using hyx
  obtain ⟨W, hW, hyW, -, kk, hdiv⟩ := hJdiv Y ρ hE y j hyj
  have hWη : genericPoint Y ∈ W := gen_mem hyW
  have key : ∀ c : Γ(X, U j), fnOf W hWη ((ρ.appLE (U j) W hW).hom c) = φ (fnOf (U j) (hη j) c) := by
    intro c
    rw [hfn (U j) (hη j) (hW hWη) c]
    exact fnOf_resG hW hWη ((ρ.app (U j)).hom c)
  have hbne : φ (fnOf (U j) (hη j) (b j)) ≠ 0 := by
    rw [map_ne_zero]
    exact fun h0 => hb j (fnOf_injective _ _ (h0.trans (map_zero _).symm))
  have hane : φ (fnOf (U j) (hη j) (a j)) ≠ 0 := by
    rw [map_ne_zero]
    intro h0
    apply hg
    rw [← hab j, h0, zero_div]
  have hφg : φ g = φ (fnOf (U j) (hη j) (a j)) / φ (fnOf (U j) (hη j) (b j)) := by
    rw [← hab j, map_div₀]
  fin_cases kk
  · right
    obtain ⟨c, hc⟩ := hdiv 1
    have e1 := congrArg (fnOf W hWη) hc
    rw [map_mul, key, key] at e1
    have : (φ g)⁻¹ = fnOf W hWη c := by
      rw [hφg, inv_div, div_eq_iff hane]
      exact e1.trans (mul_comm _ _)
    rw [this]
    exact regAt_fnOf hyW hWη c
  · left
    obtain ⟨c, hc⟩ := hdiv 0
    have e1 := congrArg (fnOf W hWη) hc
    rw [map_mul, key, key] at e1
    have : φ g = fnOf W hWη c := by
      rw [hφg, div_eq_iff hbne]
      exact e1.trans (mul_comm _ _)
    rw [this]
    exact regAt_fnOf hyW hWη c

end GlobalTheory.RegOrInvModel
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blowup_model_regular_function_or_inverse : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ g : X.functionField, g ≠ 0 → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField), IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ ∀ y : Y, RegAt y (φ g) ∨ RegAt y (φ g)⁻¹ := by
  atlas_forward_decl GlobalTheory.RegOrInvModel.exists_model_regAt_or_regAt_inv
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem exists_model_list (k : Type) [CommRing k] (D : ℕ) (L : ℕ) :
    ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), IsArithVar p D →
    ∀ (g : List X.functionField), g.length = L → (∀ h ∈ g, h ≠ 0) →
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField),
      IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ ∀ h ∈ g, ∀ y : Y, RegAt y (φ h) ∨ RegAt y (φ h)⁻¹ := by
  induction L with
  | zero =>
    intro X _ p hp g hg _
    obtain rfl := List.length_eq_zero_iff.1 hg
    refine ⟨X, inferInstance, 𝟙 X, RingHom.id _, by simpa using hp, (GlobalTheory.T.isBirationalModel_id_and_comp X X X (𝟙 X) (𝟙 X)
      (RingHom.id _) (RingHom.id _)).1, by simp⟩
  | succ n ih =>
    intro X _ p hp g hg hne
    obtain ⟨a, g', rfl⟩ : ∃ a g', g = a :: g' := by
      cases g with
      | nil => simp at hg
      | cons a g' => exact ⟨a, g', rfl⟩
    obtain ⟨Y₁, hY₁, π₁, φ₁, hA₁, hM₁, hR₁⟩ :=
      ih X p hp g' (by simpa using hg) (fun h hh => hne h (List.mem_cons_of_mem _ hh))
    have ha : φ₁ a ≠ 0 := (map_ne_zero φ₁).2 (hne a List.mem_cons_self)
    obtain ⟨Y₂, hY₂, π₂, φ₂, hA₂, hM₂, hR₂⟩ := GlobalTheory.T.exists_blowup_model_regular_function_or_inverse k Y₁ (π₁ ≫ p) D hA₁ (φ₁ a) ha
    refine ⟨Y₂, hY₂, π₂ ≫ π₁, φ₂.comp φ₁, by simpa [Category.assoc] using hA₂,
      (GlobalTheory.T.isBirationalModel_id_and_comp X Y₁ Y₂ π₁ π₂ φ₁ φ₂).2 hM₁ hM₂, ?_⟩
    have hreg := (GlobalTheory.T.birationalModel_regular_unit_values k Y₁ Y₂ (π₁ ≫ p) (π₂ ≫ π₁ ≫ p) π₂ rfl φ₂ hM₂).1
    intro h hh y
    rcases List.mem_cons.1 hh with rfl | hh
    · simpa using hR₂ y
    · rcases hR₁ h hh (π₂ y) with h1 | h1
      · exact Or.inl (by simpa using hreg y _ h1)
      · exact Or.inr (by simpa [map_inv₀] using hreg y _ h1)

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem exists_model_total : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (J : Type) [Finite J] (f : J → X.functionField), (∀ j, f j ≠ 0) → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField), IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ Total (fun j => φ (f j)) := by
  intro k _ X _ p D hp J _ f hf
  have := Fintype.ofFinite J
  let g : List X.functionField := (Finset.univ : Finset (J × J)).toList.map (fun q => f q.1 / f q.2)
  have hg : ∀ j l, f j / f l ∈ g := fun j l => by
    simp only [g, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
    exact ⟨(j, l), rfl⟩
  obtain ⟨Y, hY, π, φ, hA, hM, hR⟩ := exists_model_list k D g.length X p hp g rfl (by
    intro h hh
    simp only [g, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at hh
    obtain ⟨q, rfl⟩ := hh
    exact div_ne_zero (hf q.1) (hf q.2))
  refine ⟨Y, hY, π, φ, hA, hM, fun j => (map_ne_zero φ).2 (hf j), fun y j l => ?_⟩
  rcases hR _ (hg j l) y with h | h
  · exact Or.inl (by simpa [map_div₀] using h)
  · exact Or.inr (by simpa [map_div₀, inv_div] using h)

end GlobalTheory.HSNef
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_birationalModel_totallyOrdered_family : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (J : Type) [Finite J] (f : J → X.functionField), (∀ j, f j ≠ 0) → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField), IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ Total (fun j => φ (f j)) := by
  atlas_forward_decl GlobalTheory.HSNef.exists_model_total
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

theorem smallFam_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ (B : HermLB p) (J : Type) (f : J → X.functionField) (w : J → ℝ), SmallFam B f w → SmallFam (B.pull π hπ) (fun j => φ (f j)) w := by
  intro k _ X Y _ _ p q π hπ φ hM B J f w hs
  obtain ⟨β, hβ, hreg, hnorm⟩ := hs
  obtain ⟨hR, -, hF, hV⟩ := GlobalTheory.T.birationalModel_regular_unit_values k X Y p q π hπ φ hM
  refine ⟨fun c => Units.map φ.toMonoidHom (β (c PUnit.unit)), ?_, ?_, ?_⟩
  · intro i j h
    have hi : genericPoint Y ∈ π ⁻¹ᵁ B.B.U (i PUnit.unit) :=
      LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit h.1
    have hj : genericPoint Y ∈ π ⁻¹ᵁ B.B.U (j PUnit.unit) :=
      LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit h.2
    have hX : genericPoint X ∈ B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit) := by
      rw [← hM.gen]; exact ⟨hi, hj⟩
    have eg : ((B.B.pull π).g i j).val = resG Y (fun _ hy => ⟨LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit hy.1, LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit hy.2⟩ : (B.B.pull π).U i ⊓ (B.B.pull π).U j ≤ π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit)))
        (π.app _ (B.B.g (i PUnit.unit) (j PUnit.unit)).val) := by
      dsimp only [LB.pull, LB.LinComb]
      simp only [Fintype.prod_unique, zpow_one, LB.val_res, pullU, Units.coe_map]
      rfl
    show φ (β (i PUnit.unit)) = fnOf _ h ((B.B.pull π).g i j).val * φ (β (j PUnit.unit))
    rw [hβ (i PUnit.unit) (j PUnit.unit) hX, map_mul, hF _ hX ⟨hi, hj⟩, eg]
    exact congrArg (· * φ (β (j PUnit.unit))) (fnOf_resG (X := Y) (U := π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit))) (fun _ hy => ⟨LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit hy.1, LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit hy.2⟩ : (B.B.pull π).U i ⊓ (B.B.pull π).U j ≤ π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit))) h (π.app _ (B.B.g (i PUnit.unit) (j PUnit.unit)).val)).symm
  · intro y c hy j
    show RegAt y (φ (f j) * φ (β (c PUnit.unit)))
    rw [← map_mul]
    exact hR y _ (hreg (π y) (c PUnit.unit) (LB.wchart_le B.B (fun _ : PUnit => π) c PUnit.unit hy) j)
  · intro σ z c hz j
    have hm := mem_of_mem_linComb (m := fun _ => GlobalTheory.Points.PtsOver.map π hπ _ z) (fun _ => rfl) hz
      PUnit.unit
    have hr := hreg (π (under z)) (c PUnit.unit) (mem_ptsIn.1 hm) j
    have e2 : ((B.φ σ).pull π hπ).φ c z = (B.φ σ).φ (c PUnit.unit) (GlobalTheory.Points.PtsOver.map π hπ _ z) :=
      (B.φ σ).pull_φ π hπ c z
    show ‖ratVal (φ (f j) * φ (β (c PUnit.unit))) z‖ * Real.exp (-((B.φ σ).pull π hπ).φ c z / 2) ≤ _
    rw [← map_mul, hV σ z _ hr, e2]
    exact hnorm σ _ (c PUnit.unit) hm j

end GlobalTheory.HSNef
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratFnFamilySmall_pullback_birationalModel : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ (B : HermLB p) (J : Type) (f : J → X.functionField) (w : J → ℝ), SmallFam B f w → SmallFam (B.pull π hπ) (fun j => φ (f j)) w := by
  atlas_forward_decl GlobalTheory.HSNef.smallFam_pull
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNefCore

theorem key_ineq : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (B : HermLB p) (β : ℝ), B.IsNef D → B.IsSelfInter β → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (J : Type) [Fintype J] [Nonempty J] (e : J → X.functionField) (n : J → ℕ), LinearIndependent ℤ e → SmallFam B (boxFam e x) (fun c => n c.1 * Δ) → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ β + ((D : ℝ) + 1) * (Δ + D * Real.log 2 / 2 + Real.log (Fintype.card J) / 2) * gdeg B D := by
  intro hA hAmp hSP k _ X _ p D hX B β hB hβ x Δ hx hΔ J _ _ e n he hsm

  have hne : ∀ c, boxFam e x c ≠ 0 := by
    intro c
    simp only [boxFam]
    refine mul_ne_zero (he.ne_zero c.1) ?_
    exact Finset.prod_ne_zero_iff.2 fun i _ => hx.ne_zero i
  obtain ⟨Y, hY, π, φ, hvarY, hmod, htot⟩ := GlobalTheory.T.exists_birationalModel_totallyOrdered_family k X p D hX (J × Finset (Fin D)) (boxFam e x) hne
  haveI := hY
  set q := π ≫ p with hq
  set f : J × Finset (Fin D) → Y.functionField := fun c => φ (boxFam e x c) with hf
  have hbox : f = boxFam (φ ∘ e) (φ ∘ x) := by
    funext c
    simp [hf, boxFam, map_mul, map_prod]
  have hx' : AlgebraicIndependent ℤ (φ ∘ x) := hx.map' (f := φ.toIntAlgHom) φ.injective
  have he' : LinearIndependent ℤ (φ ∘ e) :=
    he.map' φ.toIntAlgHom.toLinearMap (LinearMap.ker_eq_bot.2 φ.injective)
  set w : J × Finset (Fin D) → ℝ := fun c => n c.1 * Δ with hw
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_fubiniStudy_of_totallyOrdered_ratFnFamily k Y q (J × Finset (Fin D)) f w htot
  obtain ⟨μ, hμ⟩ : ∃ μ, M.IsSelfInter μ := by
    obtain ⟨Φ, hΦ⟩ := ((hA.arExists k Y q D hvarY).2 PUnit fun _ => M).1
    exact ⟨_, ((hA.arIso k Y q D hvarY).2 PUnit _ Φ hΦ).1 PUnit.unit⟩

  have hN : ∀ j, n j ≤ ∑ i, n i := fun j => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hchain := GlobalTheory.T.boxFamily_movingParts_chain_bound hA hAmp hSP k Y q D hvarY (φ ∘ x) Δ hx' hΔ (∑ i, n i) J (φ ∘ e) n M μ he' hN
    (hbox ▸ htot) (hbox ▸ hM) hμ

  set s : ℝ := Real.log (Fintype.card (J × Finset (Fin D))) / 2 with hs
  set B' := B.pull π rfl with hB'
  have hsmall : SmallFam B' f w := GlobalTheory.T.ratFnFamilySmall_pullback_birationalModel k X Y p q π rfl φ hmod B _ (boxFam e x) w hsm
  have hle : Le M (B'.shift (fun _ => s) fun _ => rfl) := GlobalTheory.T.fubiniStudy_le_shift_of_smallSections k Y q M B' _ f w hM hsmall
  have hle' := (GlobalTheory.T.hermLBLeBySmallSection_tensor_isometric_trans_shift k Y q (B'.shift (fun _ => s) fun _ => rfl) M M).2.2.2 Δ hle

  have hs0 : 0 ≤ s := by
    rw [hs]
    have : (1 : ℝ) ≤ Fintype.card (J × Finset (Fin D)) := by exact_mod_cast Fintype.card_pos
    have := Real.log_nonneg this
    linarith
  have hMnef : M.IsNef D := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hA k Y q D hvarY M _ f w hM fun c => by
    simp only [hw]; exact mul_nonneg (Nat.cast_nonneg _) hΔ.le
  have hB'nef : B'.IsNef D := GlobalTheory.T.hermitianLineBundle_isNef_pullback hA hSP k X Y p q D D hX hvarY π rfl B hB
  have hA1 := GlobalTheory.NefShift.isNef_shift_nonneg k Y q D hvarY B' s hs0 hB'nef
  have hA2 := GlobalTheory.NefShift.isNef_shift_nonneg k Y q D hvarY _ Δ hΔ.le hA1
  have hM2 := GlobalTheory.NefShift.isNef_shift_nonneg k Y q D hvarY M Δ hΔ.le hMnef

  obtain ⟨hg, hgs⟩ := GlobalTheory.T.geometricDegree_pull_birationalModel hA k X Y p q D hX hvarY π rfl φ hmod B
  have h1 := hgs β s hβ
  have h2 := hA.arShift k Y q D hvarY _ _ Δ h1
  have h3 := hA.arShift k Y q D hvarY M μ Δ hμ
  have hmono := GlobalTheory.T.arithSelfIntersection_mono_of_isNef hA hAmp hSP k Y q D hvarY _ _ _ _ hA2 hM2 hle' h2 h3
  rw [GlobalTheory.CovTest.GeoSwap.gdeg_shift_const, hg] at hmono

  have hcard : s = Real.log (Fintype.card J) / 2 + D * Real.log 2 / 2 := by
    rw [hs, Fintype.card_prod, Fintype.card_finset, Fintype.card_fin]
    push_cast
    rw [Real.log_mul (by exact_mod_cast Fintype.card_ne_zero) (by positivity), Real.log_pow]
    ring
  rw [hcard] at hmono
  nlinarith [hchain, hmono]

end GlobalTheory.HSNefCore
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_hermitian_small_sections_key_inequality : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (B : HermLB p) (β : ℝ), B.IsNef D → B.IsSelfInter β → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (J : Type) [Fintype J] [Nonempty J] (e : J → X.functionField) (n : J → ℕ), LinearIndependent ℤ e → SmallFam B (boxFam e x) (fun c => n c.1 * Δ) → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ β + ((D : ℝ) + 1) * (Δ + D * Real.log 2 / 2 + Real.log (Fintype.card J) / 2) * gdeg B D := by
  atlas_forward_decl GlobalTheory.HSNefCore.key_ineq
end

section
section
open Filter Topology

namespace GlobalTheory

theorem exists_linearIndependent_finCons_of_lt {G : Type} [AddCommGroup G] {m k : ℕ}
    (e : Fin m → G) (he : LinearIndependent ℤ e) (f : Fin k → G) (hf : LinearIndependent ℤ f)
    (hmk : m < k) : ∃ j, LinearIndependent ℤ (Fin.cons (f j) e : Fin m.succ → G) := by
  classical
  by_contra hcon
  push_neg at hcon
  have hc : ∀ j, ∃ c : ℤ, c ≠ 0 ∧ c • f j ∈ Submodule.span ℤ (Set.range e) := by
    intro j
    by_contra h
    push_neg at h
    apply hcon j
    refine LinearIndependent.finCons' (f j) e he fun c y hy hxy => ?_
    by_contra hc0
    apply h c hc0
    have : c • f j = -y := eq_neg_of_add_eq_zero_left hxy
    rw [this]
    exact Submodule.neg_mem _ hy
  choose c hc0 hcs using hc
  have hg : LinearIndependent ℤ (fun j => c j • f j) := by
    rw [Fintype.linearIndependent_iff] at hf ⊢
    intro a ha j
    have := hf (fun j => a j * c j) (by simpa [mul_smul] using ha) j
    exact (mul_eq_zero.mp this).resolve_right (hc0 j)
  have hle := linearIndependent_le_span_aux' (fun j => c j • f j) hg (Set.range e)
    (by rintro _ ⟨j, rfl⟩; exact hcs j)
  have h2 : Fintype.card (Set.range e) = m := by
    rw [Set.card_range_of_injective he.injective, Fintype.card_fin]
  rw [h2, Fintype.card_fin] at hle
  omega

theorem exists_linearIndependent_extend_with_levels {G : Type} [AddCommGroup G] (S : ℕ → Set G) {k : ℕ} (f : Fin k → G)
    (hf : LinearIndependent ℤ f) (hfS : ∀ j, f j ∈ S 0) (m : ℕ) (e : Fin m → G) (n : Fin m → ℕ)
    (he : LinearIndependent ℤ e) (heS : ∀ j, e j ∈ S (n j)) :
    ∀ k', m ≤ k' → k' ≤ k → ∃ (e2 : Fin k' → G) (n2 : Fin k' → ℕ), LinearIndependent ℤ e2 ∧
      (∀ j, e2 j ∈ S (n2 j)) ∧ ∑ j, n2 j = ∑ j, n j := by
  intro k' hm
  induction k', hm using Nat.le_induction with
  | base => intro _; exact ⟨e, n, he, heS, rfl⟩
  | succ k' hmk ih =>
    intro hk
    obtain ⟨e2, n2, h1, h2, h3⟩ := ih (by omega)
    obtain ⟨j, hj⟩ := exists_linearIndependent_finCons_of_lt e2 h1 f hf (by omega)
    refine ⟨Fin.cons (f j) e2, Fin.cons 0 n2, hj, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hfS j
      · simpa using h2 i
    · rw [Fin.sum_cons, zero_add, h3]

theorem exists_linearIndependent_adapted_to_decreasing_chain : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G]
    (S : ℕ → Set G), (∀ i, S (i + 1) ⊆ S i) → ∀ (N : ℕ) (r : ℕ → ℕ),
    (∀ i, ∃ e : Fin (r i) → G, LinearIndependent ℤ e ∧ ∀ j, e j ∈ S i) →
    (∀ i, r (i + 1) ≤ r i) → ∃ (e : Fin (r 0) → G) (n : Fin (r 0) → ℕ),
      LinearIndependent ℤ e ∧ (∀ j, e j ∈ S (n j)) ∧
      ∑ i ∈ Finset.range (N + 1), r i ≤ ∑ j, (n j + 1) := by
  intro G _ _ S hS N
  induction N generalizing S with
  | zero =>
    intro r hr _
    obtain ⟨e, he, heS⟩ := hr 0
    exact ⟨e, fun _ => 0, he, heS, by simp⟩
  | succ N ih =>
    intro r hr hrd
    obtain ⟨e', n', he', heS', hsum⟩ := ih (fun i => S (i + 1)) (fun i => hS (i + 1))
      (fun i => r (i + 1)) (fun i => hr (i + 1)) (fun i => hrd (i + 1))
    obtain ⟨f, hf, hfS⟩ := hr 0
    obtain ⟨e, n, he, heS, hn⟩ := exists_linearIndependent_extend_with_levels S f hf hfS (r (0 + 1)) e' (fun j => n' j + 1) he'
      heS' (r 0) (hrd 0) le_rfl
    refine ⟨e, n, he, heS, ?_⟩
    rw [Finset.sum_range_succ']
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at hsum hn ⊢
    omega

end GlobalTheory
end

open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearIndependent_adapted_to_decreasing_chain' : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (S : ℕ → Set G), (∀ i, S (i + 1) ⊆ S i) → ∀ (N : ℕ) (r : ℕ → ℕ), (∀ i, ∃ e : Fin (r i) → G, LinearIndependent ℤ e ∧ ∀ j, e j ∈ S i) → (∀ i, r (i + 1) ≤ r i) → ∃ (e : Fin (r 0) → G) (n : Fin (r 0) → ℕ), LinearIndependent ℤ e ∧ (∀ j, e j ∈ S (n j)) ∧ ∑ i ∈ Finset.range (N + 1), r i ≤ ∑ j, (n j + 1) := by
  atlas_forward_decl GlobalTheory.exists_linearIndependent_adapted_to_decreasing_chain
end

section
section
open Filter Topology
open GlobalTheory GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem finrank_span_finset_le_of_indep {G : Type} [AddCommGroup G] [IsAddTorsionFree G] (T : Finset G) (r : ℕ)
    (hr : ∀ (n : ℕ) (e : Fin n → G), LinearIndependent ℤ e → (∀ j, e j ∈ (T : Set G)) → n ≤ r) :
    Module.finrank ℤ (Submodule.span ℤ (T : Set G)) ≤ r := by
  classical
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn ℤ (Subtype.val : ↥(T : Set G) → G)
  have ha : ∀ i : (T : Set G), ∃ a : ℤ, a ≠ 0 ∧ a • (i : G) ∈ Submodule.span ℤ (Subtype.val '' s) := by
    intro i
    by_cases h : i ∈ s
    · exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span ⟨i, h, rfl⟩⟩
    · exact hmax i h
  choose a ha0 ha using ha
  set M : ℤ := ∏ i, a i with hMdef
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => ha0 i)
  have hMmem : ∀ x ∈ Submodule.span ℤ (T : Set G), M • x ∈ Submodule.span ℤ (Subtype.val '' s) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      have e : M = a ⟨y, hy⟩ * ∏ i ∈ Finset.univ.erase ⟨y, hy⟩, a i :=
        (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
      rw [e, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ (ha ⟨y, hy⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  let f : Submodule.span ℤ (T : Set G) →ₗ[ℤ] Submodule.span ℤ (Subtype.val '' s) :=
    { toFun := fun x => ⟨M • (x : G), hMmem x x.2⟩
      map_add' := by intro x y; ext; simp [smul_add]
      map_smul' := by
        intro c x; ext
        change M • (c • (x : G)) = c • (M • (x : G))
        exact smul_comm _ _ _ }
  have hf : Function.Injective f := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    exact Subtype.ext (smul_right_injective G hM0 e)
  have hsfin : (Subtype.val '' s : Set G).Finite := (Set.toFinite s).image _
  haveI : Module.Finite ℤ (Submodule.span ℤ (Subtype.val '' s)) := Module.Finite.span_of_finite ℤ hsfin
  have h1 := LinearMap.finrank_le_finrank_of_injective hf
  have hli : LinearIndepOn ℤ id (Subtype.val '' s) := hs.id_image
  haveI := hsfin.fintype
  rw [finrank_span_set_eq_card hli, Set.toFinset_card] at h1
  let eqv := Fintype.equivFin (Subtype.val '' s : Set G)
  have h2 := hr _ (fun j => (eqv.symm j : G)) (hli.comp _ eqv.symm.injective) (by
    intro j
    obtain ⟨i, _, hi⟩ := (eqv.symm j).2
    rw [← hi]; exact i.2)
  exact h1.trans h2

theorem encard_finset_le_pow_mul {G : Type} [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G)
    (B : ℝ → Set G) (hB : IsBallFam Λ B) (R : ℝ) (q r : ℕ) (hq : 0 < q)
    (hr : ∀ (n : ℕ) (e : Fin n → G), LinearIndependent ℤ e → (∀ j, e j ∈ B R) → n ≤ r)
    (T : Finset G) (hT : (T : Set G) ⊆ B R) :
    (T : Set G).encard ≤ ((q ^ r : ℕ) : ℕ∞) * (B (2 * R / q)).encard := by
  classical
  haveI : NeZero q := ⟨hq.ne'⟩
  set L := Submodule.span ℤ (T : Set G) with hLdef
  have hd : Module.finrank ℤ L ≤ r :=
    finrank_span_finset_le_of_indep T r (fun n e he hmem => hr n e he (fun j => hT (hmem j)))
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  set d := Module.finrank ℤ L with hddef
  let b := Module.finBasis ℤ L
  let v : G → (Fin d → ℤ) := fun x => if hx : x ∈ L then b.equivFun ⟨x, hx⟩ else 0
  let c : G → (Fin d → ZMod q) := fun x i => ((v x i : ℤ) : ZMod q)
  let z : G → G → G := fun x y => ((b.equivFun.symm (fun i => (v x i - v y i) / (q : ℤ)) : L) : G)
  have hkey : ∀ x ∈ L, ∀ y ∈ L, c x = c y → q • z x y = x - y := by
    intro x hx y hy hc
    have hdvd : ∀ i, (q : ℤ) ∣ v x i - v y i := by
      intro i
      have e := congrFun hc i
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
      push_cast
      exact sub_eq_zero.2 e
    have hvx : v x = b.equivFun ⟨x, hx⟩ := dif_pos hx
    have hvy : v y = b.equivFun ⟨y, hy⟩ := dif_pos hy
    have e : q • (b.equivFun.symm (fun i => (v x i - v y i) / (q : ℤ)) : L) = ⟨x, hx⟩ - ⟨y, hy⟩ := by
      apply b.equivFun.injective
      rw [map_nsmul, LinearEquiv.apply_symm_apply, map_sub, ← hvx, ← hvy]
      funext i
      simp only [Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul]
      exact Int.mul_ediv_cancel' (hdvd i)
    have e2 := congrArg Subtype.val e
    simpa [z] using e2
  have hLΛ : ∀ x ∈ L, x ∈ Λ := by
    intro x hx
    have : L ≤ Λ.toIntSubmodule := Submodule.span_le.2 (fun y hy => hB.subset R (hT hy))
    exact this hx
  let ρ : (Fin d → ZMod q) → G := Function.invFunOn c (T : Set G)
  have hρ : ∀ x ∈ (T : Set G), ρ (c x) ∈ (T : Set G) ∧ c (ρ (c x)) = c x := fun x hx =>
    ⟨Function.invFunOn_mem ⟨x, hx, rfl⟩, Function.invFunOn_eq ⟨x, hx, rfl⟩⟩
  let φ : G → (Fin d → ZMod q) × G := fun x => (c x, z x (ρ (c x)))
  have hsub : ∀ x ∈ (T : Set G), x ∈ L := fun x hx => Submodule.subset_span hx
  have hmaps : Set.MapsTo φ (T : Set G) (Set.univ ×ˢ B (2 * R / q)) := by
    intro x hx
    refine ⟨Set.mem_univ _, ?_⟩
    obtain ⟨hyT, hyc⟩ := hρ x hx
    have h1 := hkey x (hsub x hx) _ (hsub _ hyT) hyc.symm
    have h2 : x - ρ (c x) ∈ B (R + R) := hB.sub_mem R R _ _ (hT hx) (hT hyT)
    have hqR : ((q : ℝ)) * (2 * R / q) = R + R := by
      have : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      field_simp; ring
    have hzΛ : z x (ρ (c x)) ∈ Λ := hLΛ _ (Subtype.property _)
    refine (hB.nsmul_iff q (2 * R / q) _ hq hzΛ).1 ?_
    rw [hqR, h1]; exact h2
  have hinj : Set.InjOn φ (T : Set G) := by
    intro x hx x' hx' h
    have hc : c x = c x' := congrArg Prod.fst h
    have hz : z x (ρ (c x)) = z x' (ρ (c x')) := congrArg Prod.snd h
    obtain ⟨hyT, hyc⟩ := hρ x hx
    have h1 := hkey x (hsub x hx) _ (hsub _ hyT) hyc.symm
    have h1' := hkey x' (hsub x' hx') (ρ (c x)) (hsub _ hyT) (by rw [hyc, hc])
    rw [← hc] at hz
    rw [hz] at h1
    exact sub_left_injective (h1.symm.trans h1')
  have hle := Set.encard_le_encard_of_injOn hmaps hinj
  rw [Set.encard_prod, Set.encard_univ] at hle
  refine hle.trans ?_
  gcongr
  rw [ENat.card_eq_coe_fintype_card]
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  exact_mod_cast Nat.pow_le_pow_right hq hd

theorem encard_ball_le_pow_mul : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G) (B : ℝ → Set G),
    IsBallFam Λ B → ∀ (R : ℝ) (q r : ℕ), 0 < q →
    (∀ (n : ℕ) (e : Fin n → G), LinearIndependent ℤ e → (∀ j, e j ∈ B R) → n ≤ r) →
    (B R).encard ≤ ((q ^ r : ℕ) : ℕ∞) * (B (2 * R / q)).encard := by
  intro G _ _ Λ B hB R q r hq hr
  by_contra hlt
  push_neg at hlt
  have hC := hlt.ne_top
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt hlt)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hC
  have htfin : t.Finite := Set.encard_ne_top_iff.1 (by rw [htc, ← hm]; exact ENat.coe_ne_top (m + 1))
  have h := encard_finset_le_pow_mul Λ B hB R q r hq hr htfin.toFinset (by simpa using hts)
  rw [Set.Finite.coe_toFinset, htc, ← hm] at h
  norm_cast at h
  omega

end GlobalTheory.VolBr
end

open Filter Topology
open GlobalTheory GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_seminormBall_le_pow_mul_smaller : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ (R : ℝ) (q r : ℕ), 0 < q → (∀ (n : ℕ) (e : Fin n → G), LinearIndependent ℤ e → (∀ j, e j ∈ B R) → n ≤ r) → (B R).encard ≤ ((q ^ r : ℕ) : ℕ∞) * (B (2 * R / q)).encard := by
  atlas_forward_decl GlobalTheory.VolBr.encard_ball_le_pow_mul
end

section
section
open Filter Topology
open GlobalTheory GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_ncard_unit_ball_le_of_indep_bound :
    ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B →
      (B 1).Finite → ∀ (q : ℕ) (T : ℝ), 3 ≤ q → 0 ≤ T →
      (∀ (r : ℕ) (e : Fin r → G) (n : Fin r → ℕ), LinearIndependent ℤ e → (∀ j, e j ∈ B ((2 / q : ℝ) ^ n j)) →
        ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ T) → Real.log ((B 1).ncard : ℝ) ≤ Real.log q * T := by
  classical
  intro G _ _ Λ B hB hfin q T hq hT hbound
  set S : ℕ → Set G := fun i => B ((2 / q : ℝ) ^ i) with hS
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hmono := (isBallFam_mono_neg_add G Λ B hB).1
  have hSdec : ∀ i, S (i + 1) ⊆ S i := by
    intro i
    apply hmono
    have h0 : (0 : ℝ) ≤ 2 / q := by positivity
    have h1 : (2 / q : ℝ) ≤ 1 := by
      rw [div_le_one hqpos]; exact_mod_cast (by omega : 2 ≤ q)
    exact pow_le_pow_of_le_one h0 h1 (Nat.le_succ i)
  set K : ℕ := ⌊T⌋₊ with hK

  have hsize : ∀ i m (e : Fin m → G), LinearIndependent ℤ e → (∀ j, e j ∈ S i) → m ≤ K := by
    intro i m e he hmem
    have h := hbound m e (fun _ => i) he hmem
    apply Nat.le_floor
    refine le_trans ?_ h
    have : m ≤ ∑ _j : Fin m, (i + 1) := by simp; exact Nat.le_mul_of_pos_right m (Nat.succ_pos i)
    exact_mod_cast this
  let P : ℕ → ℕ → Prop := fun i m => ∃ e : Fin m → G, LinearIndependent ℤ e ∧ ∀ j, e j ∈ S i
  let r : ℕ → ℕ := fun i => Nat.findGreatest (P i) K
  have hP0 : ∀ i, P i 0 := fun i => ⟨Fin.elim0, linearIndependent_empty_type, fun j => j.elim0⟩
  have hrspec : ∀ i, P i (r i) := fun i => Nat.findGreatest_spec (Nat.zero_le K) (hP0 i)
  have hrmax : ∀ i m (e : Fin m → G), LinearIndependent ℤ e → (∀ j, e j ∈ S i) → m ≤ r i := by
    intro i m e he hmem
    exact Nat.le_findGreatest (hsize i m e he hmem) ⟨e, he, hmem⟩
  have hrdec : ∀ i, r (i + 1) ≤ r i := by
    intro i
    obtain ⟨e, he, hmem⟩ := hrspec (i + 1)
    exact hrmax i _ e he (fun j => hSdec i (hmem j))

  have hstep : ∀ i, (S i).encard ≤ ((q ^ r i : ℕ) : ℕ∞) * (S (i + 1)).encard := by
    intro i
    have h := GlobalTheory.T.encard_seminormBall_le_pow_mul_smaller G Λ B hB ((2 / q : ℝ) ^ i) q (r i) (by omega)
      (fun n e he hmem => hrmax i n e he hmem)
    have heq : 2 * (2 / q : ℝ) ^ i / q = (2 / q : ℝ) ^ (i + 1) := by
      rw [pow_succ]; ring
    simpa [hS, heq] using h
  have hiter : ∀ k, (S 0).encard ≤ ((q ^ (∑ i ∈ Finset.range k, r i) : ℕ) : ℕ∞) * (S k).encard := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      refine ih.trans ?_
      rw [Finset.sum_range_succ, pow_add, Nat.cast_mul, mul_assoc]
      gcongr
      exact hstep k

  have hSK : S K ⊆ {0} := by
    intro x hx
    by_contra hx0
    have hli : LinearIndependent ℤ (fun _ : Fin 1 => x) := by
      rw [linearIndependent_unique_iff]; exact hx0
    have h := hbound 1 (fun _ => x) (fun _ => K) hli (fun _ => hx)
    have hlt : T < (K : ℝ) + 1 := Nat.lt_floor_add_one T
    simp at h
    linarith
  have hSK1 : (S K).encard ≤ 1 := by
    calc (S K).encard ≤ ({0} : Set G).encard := Set.encard_le_encard hSK
      _ = 1 := Set.encard_singleton 0

  obtain ⟨e, n, he, hmem, hsum⟩ := GlobalTheory.T.exists_linearIndependent_adapted_to_decreasing_chain' G S hSdec K r hrspec hrdec
  have hM : ((∑ i ∈ Finset.range K, r i : ℕ) : ℝ) ≤ T := by
    have h1 := hbound (r 0) e n he hmem
    have h2 : ∑ i ∈ Finset.range K, r i ≤ ∑ i ∈ Finset.range (K + 1), r i :=
      Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ K))
    have h3 : ((∑ i ∈ Finset.range K, r i : ℕ) : ℝ) ≤ ((∑ j, (n j + 1) : ℕ) : ℝ) := by
      exact_mod_cast h2.trans hsum
    linarith
  set M := ∑ i ∈ Finset.range K, r i with hMdef
  have hS0 : S 0 = B 1 := by simp [hS]
  have hcard : (B 1).encard ≤ ((q ^ M : ℕ) : ℕ∞) := by
    rw [← hS0]
    calc (S 0).encard ≤ ((q ^ M : ℕ) : ℕ∞) * (S K).encard := hiter K
      _ ≤ ((q ^ M : ℕ) : ℕ∞) * 1 := by gcongr
      _ = _ := mul_one _
  have hncard : (B 1).ncard ≤ q ^ M := by
    rw [← hfin.cast_ncard_eq] at hcard
    exact_mod_cast hcard
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  rcases Nat.eq_zero_or_pos (B 1).ncard with h0 | hpos
  · rw [h0]; simp; positivity
  · have hpos' : (0 : ℝ) < (B 1).ncard := by exact_mod_cast hpos
    calc Real.log ((B 1).ncard : ℝ) ≤ Real.log ((q ^ M : ℕ) : ℝ) :=
          Real.log_le_log hpos' (by exact_mod_cast hncard)
      _ = M * Real.log q := by rw [Nat.cast_pow, Real.log_pow]
      _ ≤ T * Real.log q := by gcongr
      _ = Real.log q * T := mul_comm _ _

end GlobalTheory.VolBr

example : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → (B 1).Finite → ∀ (q : ℕ) (T : ℝ), 3 ≤ q → 0 ≤ T → (∀ (r : ℕ) (e : Fin r → G) (n : Fin r → ℕ), LinearIndependent ℤ e → (∀ j, e j ∈ B ((2 / q : ℝ) ^ n j)) → ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ T) → Real.log ((B 1).ncard : ℝ) ≤ Real.log q * T := GlobalTheory.VolBr.log_ncard_unit_ball_le_of_indep_bound
end

open Filter Topology
open GlobalTheory GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_ncard_unitBall_le_of_independent_level_bound : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → (B 1).Finite → ∀ (q : ℕ) (T : ℝ), 3 ≤ q → 0 ≤ T → (∀ (r : ℕ) (e : Fin r → G) (n : Fin r → ℕ), LinearIndependent ℤ e → (∀ j, e j ∈ B ((2 / q : ℝ) ^ n j)) → ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ T) → Real.log ((B 1).ncard : ℝ) ≤ Real.log q * T := by
  atlas_forward_decl GlobalTheory.VolBr.log_ncard_unit_ball_le_of_indep_bound
end

section
open Filter Topology

namespace GlobalTheory

theorem le_add_mul_log_sq_of_le_add_mul_log :
    ∀ (α β r s : ℝ), 0 ≤ α → 0 ≤ β → 1 ≤ r → r ≤ s → s ≤ α + β * Real.log r →
      s ≤ α + β * Real.log ((α + 2 * β + 1) ^ 2) := by
  intro α β r s hα hβ hr hrs hs
  have hr0 : 0 < r := by linarith
  set t := Real.sqrt r with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg r
  have htt : t * t = r := Real.mul_self_sqrt hr0.le
  have ht1 : 1 ≤ t := by
    by_contra h
    push_neg at h
    nlinarith
  have htpos : 0 < t := by linarith
  have hlog : Real.log r ≤ 2 * t - 2 := by
    have h1 : Real.log r = 2 * Real.log t := by
      rw [← htt, Real.log_mul htpos.ne' htpos.ne']; ring
    have h2 := Real.log_le_sub_one_of_pos htpos
    linarith
  have hle : t ≤ α + 2 * β + 1 := by
    by_contra h
    push_neg at h
    nlinarith [mul_lt_mul_of_pos_left h htpos, mul_nonneg hα (sub_nonneg.mpr ht1),
      mul_le_mul_of_nonneg_left hlog hβ]
  have hrc : r ≤ (α + 2 * β + 1) ^ 2 := by
    rw [← htt]; nlinarith
  have hl : Real.log r ≤ Real.log ((α + 2 * β + 1) ^ 2) := Real.log_le_log hr0 hrc
  nlinarith [mul_le_mul_of_nonneg_left hl hβ]

end GlobalTheory
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem smallFam_pair_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (J : Type) (f : J → X.functionField) (w : J → ℝ), (∀ j, f j ∈ P.Bl 1 1 (Real.exp (-w j))) → SmallFam (P.L.tens P.A) f w := by
  intro k _ X _ p P J f w hf
  have e (c : (P.L.tens P.A).B.ι) (j : J) :
      f j * (((P.r c.1 * P.r' c.2 : X.functionFieldˣ)) : X.functionField) = P.loc 1 1 (f j) c.1 c.2 := by
    simp only [Pair.loc, Units.val_mul, zpow_one]; ring
  refine ⟨fun c => P.r c.1 * P.r' c.2, GlobalTheory.PtHtComb.isRatSec_tens P.hr P.hr', ?_, ?_⟩
  · intro x c hc j
    rw [e]
    exact (hf j).1 x c.1 c.2 hc.1 hc.2
  · intro σ y c hc j
    obtain ⟨hc₁, hc₂⟩ := mem_ptsIn_inf.1 hc
    have h := nu_eq k X p P 1 1 (f j) (hf j).1 σ y c.1 c.2 hc₁ hc₂
    have hb := (hf j).2 σ y
    rw [h] at hb
    rw [e]
    change _ * Real.exp (-((P.L.φ σ).φ c.1 y + (P.A.φ σ).φ c.2 y) / 2) ≤ _
    simpa using hb

end GlobalTheory.HSNef
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallSections_pairSum_ratFnFamily_tensor : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (J : Type) (f : J → X.functionField) (w : J → ℝ), (∀ j, f j ∈ P.Bl 1 1 (Real.exp (-w j))) → SmallFam (P.L.tens P.A) f w := by
  atlas_forward_decl GlobalTheory.HSNef.smallFam_pair_tens
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem GlobalTheory.HSNef.lc_le_bound : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (x : Fin D → X.functionField) (β : ℝ) (q : ℕ), AlgebraicIndependent ℤ x → (∀ S : Finset (Fin D), ∏ i ∈ S, x i ∈ P.Bl 0 1 1) → (P.L.tens P.A).IsNef D → (P.L.tens P.A).IsSelfInter β → 3 ≤ q → P.lc 1 0 1 ≤ bound D q β (gdeg (P.L.tens P.A) D) := by
  intro hC hA hS k _ X _ p D hX P x β q hx hxB hNef hSI hq
  haveI := hX.charZero
  haveI hcz : CharZero X.functionField :=
    charZero_of_injective_ringHom (f := (X.germToFunctionField ⊤).hom) (X.germToFunctionField_injective ⊤)
  have hβ : 0 ≤ β := by
    obtain ⟨h, hh, rfl⟩ := hSI
    exact (GlobalTheory.T.arithKleiman_heightNef_of_isNef hC hA hS k X p D hX _ hNef).2 h hh _
  have hg : 0 ≤ gdeg (P.L.tens P.A) D := GlobalTheory.T.hermLineBundleGeometricDegree_nonneg_of_semiPos k X p D hX _ hNef.semiPos
  have hq' : (3:ℝ) ≤ q := by exact_mod_cast hq
  have hΔ : 0 < Real.log ((q:ℝ)/2) := Real.log_pos (by linarith)
  have hF : (0:ℝ) < ((D+1).factorial : ℝ) := by positivity
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hFD : 0 < ((D+1).factorial : ℝ) * Real.log ((q:ℝ)/2) := mul_pos hF hΔ
  set g := gdeg (P.L.tens P.A) D with hgdef
  set Δ := Real.log ((q:ℝ)/2) with hΔdef
  set α := (β + (D + 1) * (Δ + D * Real.log 2 / 2) * g) / ((D + 1).factorial * Δ) with hαdef
  set β' := (D + 1) * g / (2 * ((D + 1).factorial * Δ)) with hβ'def
  have hα : 0 ≤ α := div_nonneg (by positivity) hFD.le
  have hβ' : 0 ≤ β' := div_nonneg (by positivity) (by positivity)
  have hT : 0 ≤ α + β' * Real.log ((α + 2 * β' + 1) ^ 2) :=
    add_nonneg hα (mul_nonneg hβ' (Real.log_nonneg (by nlinarith)))
  have hexp : ∀ m : ℕ, (2 / q : ℝ) ^ m = Real.exp (-(m * Δ)) := by
    intro m
    have e1 : (2 / q : ℝ) = Real.exp (-Δ) := by
      rw [Real.exp_neg, hΔdef, Real.exp_log (by positivity), inv_div]
    rw [e1, ← Real.exp_nat_mul]
    congr 1
    ring
  have key : ∀ (r : ℕ) (e : Fin r → X.functionField) (n : Fin r → ℕ), LinearIndependent ℤ e →
      (∀ j, e j ∈ P.Bl 1 0 ((2 / q : ℝ) ^ n j)) →
      ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ α + β' * Real.log ((α + 2 * β' + 1) ^ 2) := by
    intro r e n he hB
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simpa using hT
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    have hsmall : SmallFam (P.L.tens P.A) (boxFam e x) (fun c => n c.1 * Δ) := by
      apply GlobalTheory.T.smallSections_pairSum_ratFnFamily_tensor k X p P
      rintro ⟨j, S⟩
      have h1 := hB j
      have h2 := hxB S
      obtain ⟨hm, hnu⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P 1 0 0 1 _ _ h1.1 h2.1
      have e10 : ((1:ℤ) + 0) = 1 := by norm_num
      have e01 : ((0:ℤ) + 1) = 1 := by norm_num
      rw [e10, e01] at hm hnu
      refine ⟨hm, fun σ y => ?_⟩
      show P.nu 1 1 σ y (e j * ∏ i ∈ S, x i) ≤ _
      rw [hnu, ← hexp]
      have h0 : 0 ≤ P.nu 1 0 σ y (e j) := by unfold Pair.nu; positivity
      exact (mul_le_of_le_one_right h0 (h2.2 σ y)).trans (h1.2 σ y)
    have hcore := GlobalTheory.T.nef_hermitian_small_sections_key_inequality hC hA hS k X p D hX _ β hNef hSI x Δ hx hΔ (Fin r) e n he hsmall
    rw [Fintype.card_fin] at hcore
    have hrs : (r:ℝ) ≤ ((∑ j, (n j + 1) : ℕ) : ℝ) := by
      have : r ≤ ∑ j : Fin r, (n j + 1) := by
        calc r = ∑ _j : Fin r, 1 := by simp
          _ ≤ _ := Finset.sum_le_sum (fun j _ => by omega)
      exact_mod_cast this
    have hs : ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ α + β' * Real.log r := by
      have e2 : α + β' * Real.log r =
          (β + ((D:ℝ) + 1) * (Δ + D * Real.log 2 / 2 + Real.log r / 2) * g) / ((D + 1).factorial * Δ) := by
        rw [hαdef, hβ'def]
        field_simp
        ring
      rw [e2, le_div_iff₀ hFD]
      linarith
    exact GlobalTheory.le_add_mul_log_sq_of_le_add_mul_log α β' r _ hα hβ' (by exact_mod_cast hr) hrs hs
  have hfin := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P 1 0 1
  exact GlobalTheory.T.log_ncard_unitBall_le_of_independent_level_bound X.functionField (P.H 1 0) (P.Bl 1 0) (GlobalTheory.VolBr.Pair.isBallFam k X p P 1 0) hfin q _ hq hT key
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_log_small_sections_upper_bound : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (x : Fin D → X.functionField) (β : ℝ) (q : ℕ), AlgebraicIndependent ℤ x → (∀ S : Finset (Fin D), ∏ i ∈ S, x i ∈ P.Bl 0 1 1) → (P.L.tens P.A).IsNef D → (P.L.tens P.A).IsSelfInter β → 3 ≤ q → P.lc 1 0 1 ≤ bound D q β (gdeg (P.L.tens P.A) D) := by
  atlas_forward_decl GlobalTheory.HSNef.lc_le_bound
end
