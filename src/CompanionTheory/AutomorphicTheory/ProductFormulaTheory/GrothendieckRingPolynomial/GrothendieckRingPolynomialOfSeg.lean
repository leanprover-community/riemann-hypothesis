import Mathlib
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassGlEqClass
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassProductIrreducibleLeft
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTwoBlocksEmptyProductLeftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquivStatement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivProdIrrZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GelfandKazhdanContragredientImports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LocalLanglandsOfIrreducibleAdmissibleImports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ProductTransposeInverseDualReverseImports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ContragredientProductIrreducibleImports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DualClassInvolutiveImports
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGLStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsRepOrderedWordOccurs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffle
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordOccursOfSubquotientImports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedWordLettersCuspidal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsMutualShuffleEqStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShufflePermFlatten
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalSegmentsReverseOrdered
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCanonicalSegmentOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductPermEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalProductEquivMultiplicityOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.JacquetMultiplicityPosImports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOfEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLengthStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursIrreducibleSubquotient
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.ZelevinskySegments.SegDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLe
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLengthStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentTermInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorProductDeterminesFactorClassesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.AltSum
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.ExhaustionOfSteps
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.IrreducibleAdmissibleGL
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.NotAboveTransGenSelf
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.IsLAddSegmentOfInjectiveOfNotPrecedes
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.JuxtPOfFineUniq
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.SquareIntegrableSegments.SegmentReordering.CsOrderfree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleOfContragredientSocleStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SocleOfMultiplicityOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductHasSocle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsFactorsDualReverseOrdered
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFreeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAllStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSegmentDual
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.LUnlinkedIrrOfSeg
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.EmbeddingMiddleFactorTriple

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.ProdReorder

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace GrothendieckAssociativity

theorem class_congr_equiv {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W}
    (φ : Nonempty (π.Equiv τ)) : cl0 π = cl0 τ := by
  obtain ⟨φ⟩ := φ
  unfold cl0
  by_cases h : HasFiniteLength π
  · rw [dif_pos h, dif_pos (h.of_equiv φ)]
    exact clsGL_congr φ _ _
  · rw [dif_neg h, dif_neg (fun h' => h (h'.of_equiv φ.symm))]

theorem class_induced_cast {r t N : ℕ} (h : r + t = N) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin r) k × GL (Fin t) k) W) :
    cl0 (ind₂ (stdSum h) ρ) = cl0 (ind₂ (stdSum (rfl : r + t = r + t)) ρ) := by
  subst h
  rfl

theorem class_of_chosen_rep (x : IrrGL k) : cl0 (IrrGL.rep x) = sg x := by
  exact (dif_pos x.2.rep.hasFiniteLength).trans ((clsGL_irr x.2.rep x.2.rep.hasFiniteLength).trans
    (congrArg (fun c => Finsupp.single (⟨x.1, c⟩ : IrrGL k) (1 : ℤ)) x.2.cl_rep))

theorem mulR_sg (x y : IrrGL k) : mulR (sg x) (sg y) = cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep y)) := by
  have h1 := Finsupp.sum_single_index (a := x) (b := (1 : ℤ)) (h := fun z m => (sg y).sum fun w n => (m * n) • cl0 (prod₂ (IrrGL.rep z) (IrrGL.rep w))) (by simp only [Finsupp.sum, zero_mul, zero_smul, Finset.sum_const_zero])
  have h2 := Finsupp.sum_single_index (a := y) (b := (1 : ℤ)) (h := fun w n => ((1 : ℤ) * n) • cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep w))) (by simp only [mul_zero, zero_smul])
  exact h1.trans (h2.trans (by simp only [mul_one, one_smul]))

theorem assoc_gen (h : MulCls k) {r s t : ℕ} {V₁ V₂ V₃ U U' : Type} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U']
    (π₁ : Representation ℂ (GL (Fin r) k) V₁) (π₂ : Representation ℂ (GL (Fin s) k) V₂)
    (π₃ : Representation ℂ (GL (Fin t) k) V₃) (P : Representation ℂ (GL (Fin (r + s)) k) U)
    (R : Representation ℂ (GL (Fin (s + t)) k) U') (φ : Nonempty (P.Equiv (prod₂ π₁ π₂)))
    (ψ : Nonempty (R.Equiv (prod₂ π₂ π₃))) (s₁ : IsSmooth π₁) (s₂ : IsSmooth π₂) (s₃ : IsSmooth π₃)
    (sP : IsSmooth P) (sR : IsSmooth R) (f₁ : HasFiniteLength π₁) (f₃ : HasFiniteLength π₃)
    (fP : HasFiniteLength P) (fR : HasFiniteLength R) :
    mulR (cl0 P) (cl0 π₃) = mulR (cl0 π₁) (cl0 R) := by
  obtain ⟨a⟩ := ind₂_congr (k := k) (rfl : r + s + t = r + s + t) φ (eqv_refl π₃)
  obtain ⟨b⟩ := ind₂_assoc' (k := k) (rfl : r + s = r + s) (rfl : r + s + t = r + s + t) (rfl : s + t = s + t)
    (Nat.add_assoc r s t).symm π₁ π₂ π₃ s₁ s₂ s₃
  obtain ⟨c⟩ := ind₂_congr (k := k) (Nat.add_assoc r s t).symm (eqv_refl π₁) (eqv_symm ψ)
  have e1 : mulR (cl0 P) (cl0 π₃) = cl0 (prod₂ P π₃) := (h _ _ _ _ P π₃ fP f₃ sP s₃).2.symm
  have e2 : cl0 (prod₂ P π₃) = cl0 (ind₂ (stdSum (Nat.add_assoc r s t).symm) (extTensor π₁ R)) :=
    class_congr_equiv ⟨(a.trans b).trans c⟩
  have e3 : cl0 (ind₂ (stdSum (Nat.add_assoc r s t).symm) (extTensor π₁ R)) = cl0 (prod₂ π₁ R) :=
    class_induced_cast (Nat.add_assoc r s t).symm (extTensor π₁ R)
  have e4 : cl0 (prod₂ π₁ R) = mulR (cl0 π₁) (cl0 R) := (h _ _ _ _ π₁ R f₁ fR s₁ sR).2
  exact e1.trans (e2.trans (e3.trans e4))

end GrothendieckAssociativity

open GrothendieckAssociativity

variable (k)

theorem assoc (h : MulCls k) : Assoc k := by
  intro x y z
  have hxy : HasFiniteLength (prod₂ (IrrGL.rep x) (IrrGL.rep y)) :=
    (h x.1 y.1 _ _ (IrrGL.rep x) (IrrGL.rep y) x.2.rep.hasFiniteLength y.2.rep.hasFiniteLength
      x.2.rep.smooth y.2.rep.smooth).1
  have hyz : HasFiniteLength (prod₂ (IrrGL.rep y) (IrrGL.rep z)) :=
    (h y.1 z.1 _ _ (IrrGL.rep y) (IrrGL.rep z) y.2.rep.hasFiniteLength z.2.rep.hasFiniteLength
      y.2.rep.smooth z.2.rep.smooth).1
  have e1 : mulR (mulR (sg x) (sg y)) (sg z) = mulR (cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep y))) (cl0 (IrrGL.rep z)) :=
    (congrArg (fun a => mulR a (sg z)) (mulR_sg x y)).trans
      (congrArg (mulR (cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep y)))) (class_of_chosen_rep z).symm)
  have e2 : mulR (cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep y))) (cl0 (IrrGL.rep z)) =
      mulR (cl0 (IrrGL.rep x)) (cl0 (prod₂ (IrrGL.rep y) (IrrGL.rep z))) :=
    assoc_gen h (IrrGL.rep x) (IrrGL.rep y) (IrrGL.rep z) (prod₂ (IrrGL.rep x) (IrrGL.rep y))
      (prod₂ (IrrGL.rep y) (IrrGL.rep z)) (eqv_refl _) (eqv_refl _) x.2.rep.smooth y.2.rep.smooth
      z.2.rep.smooth (isSmooth_prod₂ _ _) (isSmooth_prod₂ _ _) x.2.rep.hasFiniteLength
      z.2.rep.hasFiniteLength hxy hyz
  have e3 : mulR (cl0 (IrrGL.rep x)) (cl0 (prod₂ (IrrGL.rep y) (IrrGL.rep z))) = mulR (sg x) (mulR (sg y) (sg z)) :=
    (congrArg (fun a => mulR a (cl0 (prod₂ (IrrGL.rep y) (IrrGL.rep z)))) (class_of_chosen_rep x)).trans
      (congrArg (mulR (sg x)) (mulR_sg y z).symm)
  exact e1.trans (e2.trans e3)

theorem one : One k := by
  intro x
  let c0 : IrrCl (GL (Fin 0) k) := (IrrRep.det (k := k) (Fin 0) 1 isSmoothChar_one).cl
  let e : (Σ _ : Fin 0, Fin 0) ≃ Fin 0 := Equiv.equivOfIsEmpty _ _
  let τ : ∀ a : Fin 0, Representation ℂ (GL (Fin ((fun _ : Fin 0 => 0) a)) k) ((fun _ : Fin 0 => ℂ) a) :=
    fun a => a.elim0
  have A : Nonempty ((multiProd e τ).Equiv (IrrRep.det (k := k) (Fin 0) 1 isSmoothChar_one).ρ) :=
    SupportRing.nonempty_equiv_unit e τ
  have B : Nonempty ((IrrGL.rep (⟨0, c0⟩ : IrrGL k)).Equiv (multiProd e τ)) :=
    eqv_trans (IrrRep.nonempty_equiv_rep _) (eqv_symm A)
  have C : Nonempty ((ind₂ (stdSum (Nat.zero_add x.1)) (extTensor (IrrGL.rep (⟨0, c0⟩ : IrrGL k)) (IrrGL.rep x))).Equiv
      (ind₂ (stdSum (Nat.zero_add x.1)) (extTensor (multiProd e τ) (IrrGL.rep x)))) :=
    ind₂_congr (k := k) (Nat.zero_add x.1) B (eqv_refl (IrrGL.rep x))
  have D : Nonempty ((ind₂ (stdSum (Nat.zero_add x.1)) (extTensor (multiProd e τ) (IrrGL.rep x))).Equiv (IrrGL.rep x)) :=
    GlobalTheory.T.parabolicInductionTwoBlocks_empty_product_left k x.1 0 (Nat.zero_add x.1) _ (IrrGL.rep x) x.2.rep.smooth (fun _ => 0) (fun _ => ℂ) τ e
  have e1 : mulR (GrothGL.unit k) (sg x) = cl0 (prod₂ (IrrGL.rep (⟨0, c0⟩ : IrrGL k)) (IrrGL.rep x)) :=
    mulR_sg _ _
  have e2 : cl0 (prod₂ (IrrGL.rep (⟨0, c0⟩ : IrrGL k)) (IrrGL.rep x)) =
      cl0 (ind₂ (stdSum (Nat.zero_add x.1)) (extTensor (IrrGL.rep (⟨0, c0⟩ : IrrGL k)) (IrrGL.rep x))) :=
    (class_induced_cast (Nat.zero_add x.1) _).symm
  obtain ⟨c⟩ := C
  obtain ⟨dd⟩ := D
  exact e1.trans (e2.trans ((class_congr_equiv ⟨c.trans dd⟩).trans (class_of_chosen_rep x)))

end CompanionTheory.Groth
end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem class_of_finite_length {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (h : HasFiniteLength π) : cl0 π = clsGL π h := by
  rw [cl0, dif_pos h]

theorem class_congr_iso {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W} (φ : π.Equiv τ) :
    cl0 π = cl0 τ := by
  by_cases h : HasFiniteLength π
  · have h' : HasFiniteLength τ := h.of_equiv φ
    rw [class_of_finite_length h, class_of_finite_length h', clsGL_congr φ h h']
  · have h' : ¬ HasFiniteLength τ := fun h' => h (h'.of_equiv φ.symm)
    rw [cl0, cl0, dif_neg h, dif_neg h']

theorem class_chosen_rep_basis (x : IrrGL k) : cl0 x.rep = sg x := by
  rw [class_of_finite_length x.2.rep.hasFiniteLength]
  exact (clsGL_irr x.2.rep _).trans (by rw [IrrCl.cl_rep]; rfl)

theorem prodIrr_cast {h h' N N' : ℕ} (e : h = h') (x : Fin h → IrrGL k) (y : Fin h' → IrrGL k)
    (hxy : ∀ i, x i = y (Fin.cast e i)) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N') :
    (HasFiniteLength (prodIrr x hx) ↔ HasFiniteLength (prodIrr y hy)) ∧
      cl0 (prodIrr x hx) = cl0 (prodIrr y hy) := by
  subst e
  have hxy' : x = y := funext fun i => hxy i
  subst hxy'
  have hN : N = N' := hx.symm.trans hy
  subst hN
  exact ⟨Iff.rfl, rfl⟩

theorem prodIrr_zero {N : ℕ} (x : Fin 0 → IrrGL k) (hd : ∑ a, (x a).1 = N) :
    HasFiniteLength (prodIrr x hd) ∧ cl0 (prodIrr x hd) = GrothGL.unit k := by
  obtain rfl : N = 0 := by simpa using hd.symm
  obtain ⟨φ⟩ := GlobalTheory.LocGL.Tests.nonempty_equiv_prodIrr_zero x hd
  have h1 : HasFiniteLength (IrrRep.det (k := k) (Fin 0) 1 isSmoothChar_one).ρ :=
    (IrrRep.det (Fin 0) 1 isSmoothChar_one).hasFiniteLength
  have hfl : HasFiniteLength (prodIrr x hd) := h1.of_equiv φ
  refine ⟨hfl, ?_⟩
  rw [← class_congr_iso φ]
  exact (class_of_finite_length h1).trans (clsGL_irr _ _)

theorem prodIrr_one (x : IrrGL k) (hd : ∑ _ : Fin 1, x.1 = x.1) :
    HasFiniteLength (prodIrr (fun _ : Fin 1 => x) hd) ∧ cl0 (prodIrr (fun _ : Fin 1 => x) hd) = sg x := by
  obtain ⟨φ⟩ := nonempty_equiv_prodIrr_one x hd
  exact ⟨x.2.rep.hasFiniteLength.of_equiv φ, (class_congr_iso φ).symm.trans (class_chosen_rep_basis x)⟩

theorem class_of_product_equiv (hM : MulCls k) {r t : ℕ} {U W X : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup X] [Module ℂ X] (π₁ : Representation ℂ (GL (Fin r) k) U)
    (π₂ : Representation ℂ (GL (Fin t) k) W) (τ : Representation ℂ (GL (Fin (r + t)) k) X)
    (F : (prod₂ π₁ π₂).Equiv τ) (h₁ : HasFiniteLength π₁) (h₂ : HasFiniteLength π₂) (s₁ : IsSmooth π₁)
    (s₂ : IsSmooth π₂) : HasFiniteLength τ ∧ cl0 τ = mulR (cl0 π₁) (cl0 π₂) := by
  obtain ⟨h, hc⟩ := hM r t U W π₁ π₂ h₁ h₂ s₁ s₂
  exact ⟨h.of_equiv F, (class_congr_iso F).symm.trans hc⟩

theorem prodIrr_append_one (hM : MulCls k) {h : ℕ} (x₀ : IrrGL k) (y : Fin h → IrrGL k)
    (hy : ∑ a, (y a).1 = ∑ a, (y a).1) (hfl : HasFiniteLength (prodIrr y hy))
    (happ : ∑ a, (Fin.append (fun _ : Fin 1 => x₀) y a).1 = x₀.1 + ∑ a, (y a).1) :
    HasFiniteLength (prodIrr (Fin.append (fun _ : Fin 1 => x₀) y) happ) ∧
      cl0 (prodIrr (Fin.append (fun _ : Fin 1 => x₀) y) happ) = mulR (sg x₀) (cl0 (prodIrr y hy)) := by
  have hx1 : ∑ _ : Fin 1, x₀.1 = x₀.1 := by simp
  obtain ⟨F⟩ := GlobalTheory.T.product_irreducible_append_equiv k 1 h x₀.1 (∑ a, (y a).1) (fun _ : Fin 1 => x₀) y hx1 hy happ
  have H1 := prodIrr_one x₀ hx1
  have H3 := class_of_product_equiv hM (prodIrr (fun _ : Fin 1 => x₀) hx1) (prodIrr y hy) _ F H1.1 hfl
    (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)
  exact ⟨H3.1, H3.2.trans (congrArg (fun a => mulR a (cl0 (prodIrr y hy))) H1.2)⟩

theorem class_product_irreducible_fold (hM : MulCls k) : ∀ (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N),
    HasFiniteLength (prodIrr x hd) ∧
      cl0 (prodIrr x hd) = (List.ofFn x).foldr (fun y a => mulR (sg y) a) (GrothGL.unit k) := by
  intro h
  induction h with
  | zero =>
    intro N x hd
    obtain ⟨hfl, hc⟩ := prodIrr_zero x hd
    refine ⟨hfl, ?_⟩
    rw [hc]
    rfl
  | succ h ih =>
    intro N x hd
    have hy : ∑ a, (Fin.tail x a).1 = ∑ a, (Fin.tail x a).1 := rfl
    have happ : ∑ a, (Fin.append (fun _ : Fin 1 => x 0) (Fin.tail x) a).1 = (x 0).1 + ∑ a, (Fin.tail x a).1 := by
      rw [Fin.sum_univ_add]
      simp
    have H2 := ih _ (Fin.tail x) hy
    have H := prodIrr_append_one hM (x 0) (Fin.tail x) hy H2.1 happ
    have hcast := prodIrr_cast (Nat.add_comm 1 h) (Fin.append (fun _ : Fin 1 => x 0) (Fin.tail x)) x
      (fun i => by rw [Fin.append_left_eq_cons, Function.comp_apply, Fin.cons_self_tail]) happ hd
    refine ⟨hcast.1.1 H.1, hcast.2.symm.trans (H.2.trans ?_)⟩
    rw [H2.2, List.ofFn_succ, List.foldr_cons]
    rfl

variable (k) in

theorem prodList (h : MulCls k) : ProdList k :=
  fun n N x hd => (class_product_irreducible_fold h n N x hd).2

end CompanionTheory.Groth

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth.GrothendieckCommutativity

section Pull

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def subComp {π : Representation ℂ G V} (s : H →* G) (S : Subrepresentation π) : Subrepresentation (π.comp s) :=
  ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (s g) hv⟩

def subQuotComp {π : Representation ℂ G V} (s : H →* G) (S T : Subrepresentation π) :
    Representation.Equiv (subQuot (subComp s S) (subComp s T)) ((subQuot S T).comp s) :=
  .mk (LinearEquiv.refl ℂ _) fun _ => rfl

def equivComp {σ : Representation ℂ G V} {τ : Representation ℂ G W} (φ : σ.Equiv τ) (s : H →* G) :
    Representation.Equiv (σ.comp s) (τ.comp s) :=
  .mk φ.toLinearEquiv fun g => φ.isIntertwining' (s g)

theorem occursTimes_comp {σ : Representation ℂ G W} {π : Representation ℂ G V} (s : H →* G) {r : ℕ}
    (h : OccursTimes σ π r) : OccursTimes (σ.comp s) (π.comp s) r := by
  obtain ⟨S, T, h1, h2, h3⟩ := h
  exact ⟨fun i => subComp s (S i), fun i => subComp s (T i), fun i => h1 i, fun i j hij => h2 i j hij,
    fun i => (h3 i).map fun φ => (subQuotComp s (S i) (T i)).trans (equivComp φ s)⟩

theorem jhMult_le_comp (σ : Representation ℂ G W) (π : Representation ℂ G V) (s : H →* G) :
    jhMult σ π ≤ jhMult (σ.comp s) (π.comp s) :=
  iSup₂_le fun r h => le_iSup₂_of_le (f := fun r (_ : OccursTimes (σ.comp s) (π.comp s) r) => (r : ℕ∞)) r
    (occursTimes_comp s h) le_rfl

end Pull

section Contra

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {π : Representation ℂ G V}

def ann (T : Subrepresentation π) : Subrepresentation (contra π) where
  toSubmodule :=
    { carrier := {l | ∀ v ∈ T.toSubmodule, (l : Module.Dual ℂ V) v = 0}
      add_mem' := fun {a b} ha hb v hv => by
        rw [Submodule.coe_add, LinearMap.add_apply, ha v hv, hb v hv, add_zero]
      zero_mem' := fun _ _ => rfl
      smul_mem' := fun c l hl v hv => by
        rw [Submodule.coe_smul, LinearMap.smul_apply, hl v hv, smul_zero] }
  apply_mem_toSubmodule g l hl v hv := by
    show (l : Module.Dual ℂ V) (π g⁻¹ v) = 0
    exact hl _ (T.apply_mem_toSubmodule g⁻¹ hv)

theorem ann_anti {S T : Subrepresentation π} (h : T ≤ S) : ann S ≤ ann T :=
  fun _ hl v hv => hl v (h hv)

variable (S T : Subrepresentation π)

def formOf (l : (ann T).toSubmodule) : Module.Dual ℂ (S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) :=
  (T.toSubmodule.comap S.toSubmodule.subtype).liftQ ((l.1 : Module.Dual ℂ V) ∘ₗ S.toSubmodule.subtype)
    fun w hw => LinearMap.mem_ker.2 (l.2 _ hw)

theorem formOf_mem (l : (ann T).toSubmodule) : formOf S T l ∈ smoothPart (subQuot S T).dual :=
  mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds l.1.2 (by
      show π.dual 1 (l.1 : Module.Dual ℂ V) = l.1
      rw [map_one]
      rfl)) fun g hg => by
    have hg' : π.dual g (l.1 : Module.Dual ℂ V) = l.1 := hg
    refine LinearMap.ext fun x => ?_
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact LinearMap.congr_fun hg' (w : V))

def annMap : (ann T).toRepresentation.IntertwiningMap (contra (subQuot S T)) where
  toLinearMap :=
    { toFun := fun l => ⟨formOf S T l, formOf_mem S T l⟩
      map_add' := fun a b => Subtype.ext (LinearMap.ext fun x => by
        obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rfl)
      map_smul' := fun c a => Subtype.ext (LinearMap.ext fun x => by
        obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rfl) }
  isIntertwining' g := LinearMap.ext fun l => Subtype.ext (LinearMap.ext fun x => by
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl)

theorem ker_annMap :
    LinearMap.ker (annMap S T).toLinearMap = (ann S).toSubmodule.comap (ann T).toSubmodule.subtype := by
  ext l
  constructor
  · intro hl v hv
    have h0 : annMap S T l = 0 := hl
    exact LinearMap.congr_fun (congrArg Subtype.val h0) (Submodule.Quotient.mk ⟨v, hv⟩)
  · intro hl
    show annMap S T l = 0
    refine Subtype.ext (LinearMap.ext fun x => ?_)
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact hl w.1 w.2

variable {S T}

theorem annMap_surjective
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (hπ : IsSmooth π) (hTS : T ≤ S) : Function.Surjective (annMap S T) := by
  intro f
  let m₀ : Module.Dual ℂ S.toSubmodule :=
    (f : Module.Dual ℂ _) ∘ₗ (T.toSubmodule.comap S.toSubmodule.subtype).mkQ
  have hSs : IsSmooth S.toRepresentation := fun w => by
    have : {g : G | S.toRepresentation g w = w} = {g : G | π g w.1 = w.1} := by
      ext g
      exact Subtype.ext_iff
    rw [this]
    exact hπ w.1
  obtain ⟨K, ho, hc, hKs⟩ := hG _ ((isSmooth_contra (subQuot S T) f).mem_nhds (by simp))
  have hm : ∀ h ∈ K, ∀ w, m₀ (S.toRepresentation h w) = m₀ w := by
    intro h hh w
    have h1 : contra (subQuot S T) h⁻¹ f = f := hKs (inv_mem hh)
    have h2 := LinearMap.congr_fun (congrArg Subtype.val h1) (Submodule.Quotient.mk w)
    rw [contra_apply, inv_inv] at h2
    exact h2
  let j : fixed S.toRepresentation K →ₗ[ℂ] fixed π K :=
    { toFun := fun w => ⟨w.1.1, GlobalTheory.ContraRefl.mem_fix.2 fun h hh =>
        congrArg Subtype.val (GlobalTheory.ContraRefl.mem_fix.1 w.2 h hh)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hj : LinearMap.ker j = ⊥ :=
    LinearMap.ker_eq_bot'.2 fun w hw => by
      have h0 := congrArg Subtype.val hw
      exact Subtype.ext (Subtype.ext h0)
  obtain ⟨j', hj'⟩ := LinearMap.exists_leftInverse_of_injective j hj
  let m : Module.Dual ℂ (fixed π K) := (m₀ ∘ₗ (fixed S.toRepresentation K).subtype) ∘ₗ j'
  obtain ⟨l, hlK, hl⟩ := GlobalTheory.ContraRefl.exists_fixed_contra hπ ho hc m
  have hlS : (l : Module.Dual ℂ V) ∘ₗ S.toSubmodule.subtype = m₀ := by
    refine GlobalTheory.ContraRefl.form_ext hSs hc (fun h hh w => ?_) hm (fun w hw => ?_)
    · have h1 := LinearMap.congr_fun (congrArg Subtype.val (hlK h⁻¹ (inv_mem hh))) (w : V)
      rw [contra_apply, inv_inv] at h1
      exact h1
    · have e1 := hl (j ⟨w, hw⟩)
      have e2 := LinearMap.congr_fun hj' ⟨w, hw⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at e2
      show (l : Module.Dual ℂ V) (w : V) = m₀ w
      rw [show (w : V) = ((j ⟨w, hw⟩ : fixed π K) : V) from rfl, e1]
      show m₀ ((fixed S.toRepresentation K).subtype (j' (j ⟨w, hw⟩))) = m₀ w
      rw [e2]
      rfl
  have hlT : l ∈ (ann T).toSubmodule := fun v hv => by
    have h1 := LinearMap.congr_fun hlS ⟨v, hTS hv⟩
    have h2 : (Submodule.Quotient.mk ⟨v, hTS hv⟩ :
        S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hv
    refine h1.trans ?_
    show f.1 ((Submodule.Quotient.mk ⟨v, hTS hv⟩ : S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype)) = 0
    rw [h2, map_zero]
  refine ⟨⟨l, hlT⟩, Subtype.ext (LinearMap.ext fun x => ?_)⟩
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact LinearMap.congr_fun hlS w

def annEquiv
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (hπ : IsSmooth π) (hTS : T ≤ S) :
    (subQuot (ann T) (ann S)).Equiv (contra (subQuot S T)) :=
  .mk ((Submodule.quotEquivOfEq _ _ (ker_annMap S T).symm).trans
      ((annMap S T).toLinearMap.quotKerEquivOfSurjective (annMap_surjective hG hπ hTS))) fun g => by
    refine LinearMap.ext fun x => ?_
    obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact LinearMap.congr_fun ((annMap S T).isIntertwining' g) l

theorem occursTimes_contra
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (hπ : IsSmooth π) {σ : Representation ℂ G W} {r : ℕ} (h : OccursTimes σ π r) :
    OccursTimes (contra σ) (contra π) r := by
  obtain ⟨S, T, h1, h2, h3⟩ := h
  exact ⟨fun i => ann (T (Fin.rev i)), fun i => ann (S (Fin.rev i)), fun i => ann_anti (h1 _),
    fun i j hij => ann_anti (h2 _ _ (Fin.rev_lt_rev.2 hij)),
    fun i => (h3 (Fin.rev i)).map fun φ =>
      (annEquiv hG hπ (h1 (Fin.rev i))).trans (GlobalTheory.ContraRefl.contraEquiv φ.symm)⟩

theorem jhMult_le_contra
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (hπ : IsSmooth π) (σ : Representation ℂ G W) : jhMult σ π ≤ jhMult (contra σ) (contra π) :=
  iSup₂_le fun r h => le_iSup₂_of_le (f := fun r (_ : OccursTimes (contra σ) (contra π) r) => (r : ℕ∞)) r
    (occursTimes_contra hG hπ h) le_rfl

end Contra

section Pairs

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prodIrr_congr {h N : ℕ} {z z' : Fin h → IrrGL k} (e : z = z') (hd : ∑ a, (z a).1 = N)
    (hd' : ∑ a, (z' a).1 = N) : Nonempty ((prodIrr z hd).Equiv (prodIrr z' hd')) := by
  subst e
  exact ⟨.refl _⟩

theorem class_product_irreducible_cast {h N M : ℕ} (e : N = M) (z : Fin h → IrrGL k) (hd : ∑ a, (z a).1 = N)
    (hd' : ∑ a, (z a).1 = M) : cl0 (prodIrr z hd) = cl0 (prodIrr z hd') := by
  subst e
  rfl

theorem hasFiniteLength_prodIrr_cast {h N M : ℕ} (e : N = M) (z : Fin h → IrrGL k) (hd : ∑ a, (z a).1 = N)
    (hd' : ∑ a, (z a).1 = M) (hf : HasFiniteLength (prodIrr z hd)) : HasFiniteLength (prodIrr z hd') := by
  subst e
  exact hf

theorem class_congr_equiv {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W} (φ : π.Equiv τ) :
    cl0 π = cl0 τ := by
  by_cases hπ : HasFiniteLength π
  · have hτ := hπ.of_equiv φ
    simp only [cl0, dif_pos hπ, dif_pos hτ]
    exact clsGL_congr φ hπ hτ
  · have hτ : ¬ HasFiniteLength τ := fun h => hπ (h.of_equiv φ.symm)
    simp only [cl0, dif_neg hπ, dif_neg hτ]

theorem class_eq_of_jordan_holder_mult {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W} (hπ : HasFiniteLength π)
    (hτ : HasFiniteLength τ) (h : ∀ σ : IrrRep (GL (Fin N) k), jhMult σ.ρ π = jhMult σ.ρ τ) : cl0 π = cl0 τ := by
  simp only [cl0, dif_pos hπ, dif_pos hτ, clsGL]
  congr 1
  ext c
  rw [cls_apply, cls_apply, h c.rep]

set_option maxHeartbeats 1000000 in

theorem jhMult_pair_le (x y : IrrGL k) {N : ℕ} (h1 : ∑ a, (![x, y] a).1 = N) (h2 : ∑ a, (![y, x] a).1 = N)
    (σ : IrrRep (GL (Fin N) k)) : jhMult σ.ρ (prodIrr ![x, y] h1) ≤ jhMult σ.ρ (prodIrr ![y, x] h2) := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hGK : GKLocal k := GlobalTheory.T.local_langlands_of_irreducible_admissible hA
  obtain ⟨hd', ⟨E1⟩⟩ := GlobalTheory.T.product_transpose_inverse_dual_reverse hA hGK ![x, y] h1
  obtain ⟨hd'', ⟨E2⟩⟩ := GlobalTheory.T.contragredient_product_irreducible hA (fun a => dualCl (![x, y] (Fin.rev a))) hd'
  have hz : (fun a => dualCl (dualCl (![x, y] (Fin.rev a)))) = ![y, x] := by
    funext a
    fin_cases a
    · exact GlobalTheory.T.dual_class_involutive hA y
    · exact GlobalTheory.T.dual_class_involutive hA x
  obtain ⟨E3⟩ := prodIrr_congr hz hd'' h2
  obtain ⟨G1⟩ := GlobalTheory.T.gelfand_kazhdan_contragredient hGK N σ.ρ σ.smooth σ.irr
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis k N
  have hσa : IsAdmissible σ.ρ := hA k N _ σ.ρ σ.smooth σ.irr
  calc jhMult σ.ρ (prodIrr ![x, y] h1)
      ≤ jhMult (σ.ρ.comp (thetaW k N)) ((prodIrr ![x, y] h1).comp (thetaW k N)) := jhMult_le_comp _ _ _
    _ = jhMult (contra σ.ρ) (prodIrr (fun a => dualCl (![x, y] (Fin.rev a))) hd') := by
        rw [jhMult_congr_left G1, jhMult_congr_right _ E1]
    _ ≤ jhMult (contra (contra σ.ρ)) (contra (prodIrr (fun a => dualCl (![x, y] (Fin.rev a))) hd')) :=
        jhMult_le_contra hG (isSmooth_prodIrr _ _) _
    _ = jhMult σ.ρ (prodIrr ![y, x] h2) := by
        rw [← jhMult_congr_left (GlobalTheory.ContraRefl.evEquiv hG hσa), jhMult_congr_right _ E2,
          jhMult_congr_right _ E3]

end Pairs

end CompanionTheory.Groth.GrothendieckCommutativity

namespace CompanionTheory.Groth

open CompanionTheory.Groth.GrothendieckCommutativity

set_option maxHeartbeats 1000000 in

theorem comm (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Comm k := by
  intro x y
  have hxy : ∑ a, (![x, y] a).1 = x.1 + y.1 := by simp [Fin.sum_univ_two]
  have hyx' : ∑ a, (![y, x] a).1 = x.1 + y.1 := by simp [Fin.sum_univ_two, add_comm]
  have hyx : ∑ a, (![y, x] a).1 = y.1 + x.1 := by simp [Fin.sum_univ_two]
  obtain ⟨E1⟩ := nonempty_prod₂_equiv_prodIrr_pair x y hxy
  obtain ⟨E2⟩ := nonempty_prod₂_equiv_prodIrr_pair y x hyx
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have f1 : HasFiniteLength (prod₂ x.rep y.rep) := GlobalTheory.T.parabolicProduct_hasFiniteLength_GL hBZ k _ _ _ _ _ _
    x.2.rep.hasFiniteLength y.2.rep.hasFiniteLength x.2.rep.smooth y.2.rep.smooth
  have f2 : HasFiniteLength (prod₂ y.rep x.rep) := GlobalTheory.T.parabolicProduct_hasFiniteLength_GL hBZ k _ _ _ _ _ _
    y.2.rep.hasFiniteLength x.2.rep.hasFiniteLength y.2.rep.smooth x.2.rep.smooth
  rw [class_congr_equiv E1, class_congr_equiv E2, ← class_product_irreducible_cast (add_comm x.1 y.1) ![y, x] hyx' hyx]
  exact class_eq_of_jordan_holder_mult (f1.of_equiv E1)
    (hasFiniteLength_prodIrr_cast (add_comm y.1 x.1) ![y, x] hyx hyx' (f2.of_equiv E2))
    fun σ => le_antisymm (jhMult_pair_le x y hxy hyx' σ) (jhMult_pair_le y x hyx' hxy σ)

end CompanionTheory.Groth

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth

section TriLemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tri_coe_decW (Δ : Segment k) : ((decW Δ : List (IrrGL k)) : Multiset (IrrGL k)) = Δ.ms := by
  have e := GlobalTheory.CompanionTheory.ZcWords.reverse_ofFn Δ.term
  rw [decW, ← e, Multiset.coe_reverse, Segment.ms, Fin.univ_val_map]

theorem tri_coe_flatten_decW (L : List (Segment k)) :
    (((L.map decW).flatten : List (IrrGL k)) : Multiset (IrrGL k)) = (L : Multiset (Segment k)).bind Segment.ms := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.flatten_cons, ← Multiset.coe_add, ih, tri_coe_decW, ← Multiset.cons_coe,
      Multiset.cons_bind]

theorem tri_msupp_of_inShW {𝔪 : Multiset (Segment k)} {w : List (IrrGL k)} (H : InShW 𝔪 w) :
    msupp 𝔪 = (w : Multiset (IrrGL k)) := by
  obtain ⟨L, rfl, hS⟩ := H
  rw [msupp, ← tri_coe_flatten_decW]
  exact (Multiset.coe_eq_coe.2 (GlobalTheory.T.perm_flatten_of_shuffle _ _ hS)).symm

theorem tri_msupp_wtW {h : ℕ} {Γ : Fin h → Segment k} {𝔫 : Multiset (Segment k)} (H : IsOrderedForm Γ 𝔫) :
    msupp 𝔫 = (wtW Γ : Multiset (IrrGL k)) := by
  have e : wtW Γ = (((List.ofFn Γ).reverse).map decW).flatten := by
    rw [wtW, GlobalTheory.CompanionTheory.ZcWords.reverse_ofFn, List.map_ofFn]
    try rfl
  rw [e, tri_coe_flatten_decW, Multiset.coe_reverse, ← Fin.univ_val_map, H.1, msupp]

theorem tri_sqLen_map_toA (𝔪 : Multiset (Segment k)) : Comb.sqLen (𝔪.map toA) = sq 𝔪 := by
  rw [Comb.sqLen, Multiset.map_map]
  rfl

end TriLemmas

theorem tri (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (c : Cls k) :
    Tri k := by
  intro 𝔪 𝔫 h x y hd hx hy hm
  obtain ⟨Δ, hΔ, hΔL⟩ := hx
  obtain ⟨h', x', hd', ⟨Γ, hΓ, -⟩, -⟩ := id hy
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have w1 : Wd y.rep (wtW Γ) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA c.soc c.jac 𝔫 y.rep hy h' Γ hΓ
  have hs : IsSubquotient y.rep (prodIrr x hd) := jhMult_ne_zero_iff.1 hm
  have w2 : Wd (prodIrr x hd) (wtW Γ) := GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr x hd) hs _ w1
  have sh : InShW (Finset.univ.val.map Δ) (wtW Γ) :=
    GlobalTheory.T.segment_product_word_in_shuffle hA c.jac x hd Δ hΔL (wtW Γ) (GlobalTheory.T.ordered_word_letters_cuspidal Γ) w2
  rw [hΔ.1] at sh
  refine ⟨(tri_msupp_of_inShW sh).trans (tri_msupp_wtW hΓ).symm, ?_⟩
  by_cases he : 𝔪 = 𝔫
  · exact Or.inl he
  right
  have hL := GlobalTheory.CompanionTheory.ZcWords.coe_map_ofFn hΓ
  have hne : 𝔪.map toA ≠ (((List.ofFn Γ).map toA : List _) : Multiset _) := by
    rw [hL]
    intro e
    exact he (Multiset.map_injective GlobalTheory.CompanionTheory.ZcWords.toA_injective e)
  have key := GlobalTheory.T.shuffle_weight_square_length_lt sNu GlobalTheory.CompanionTheory.ZcWords.sNu_injective GlobalTheory.CompanionTheory.ZcWords.sNu_aperiodic
    ((List.ofFn Γ).map toA) (𝔪.map toA) (GlobalTheory.CompanionTheory.ZcWords.aOrdered_of_isOrderedForm hΓ)
    (GlobalTheory.CompanionTheory.ZcWords.inSh_of_inShW sh) hne
  rw [hL, tri_sqLen_map_toA, tri_sqLen_map_toA] at key
  exact key

end CompanionTheory.Groth

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace GrothendieckSingleMultiplication

section Ring

theorem mulR_sg_left (a : IrrGL k) (b : GrothGL k) :
    mulR (sg a) b = b.sum fun y n => n • cl0 (prod₂ (IrrGL.rep a) (IrrGL.rep y)) := by
  unfold mulR sg
  rw [Finsupp.sum_single_index]
  · simp only [one_mul]
  · simp

theorem mulR_sg_zero (a : IrrGL k) : mulR (sg a) 0 = 0 := by
  rw [mulR_sg_left, Finsupp.sum_zero_index]

theorem mulR_sg_add (a : IrrGL k) (b c : GrothGL k) : mulR (sg a) (b + c) = mulR (sg a) b + mulR (sg a) c := by
  simp only [mulR_sg_left]
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

theorem mulR_sg_zsmul (a : IrrGL k) (n : ℤ) (b : GrothGL k) : mulR (sg a) (n • b) = n • mulR (sg a) b :=
  (AddMonoidHom.mk' (mulR (sg a)) (mulR_sg_add a)).map_zsmul n b

theorem sum_single_one_smul (T : IrrGL k → GrothGL k) (b : IrrGL k) :
    (Finsupp.single b (1 : ℤ)).sum (fun y n => n • T y) = T b := by
  rw [Finsupp.sum_single_index] <;> simp

theorem mulR_sg_sg (a b : IrrGL k) : mulR (sg a) (sg b) = cl0 (prod₂ (IrrGL.rep a) (IrrGL.rep b)) := by
  rw [mulR_sg_left]
  exact sum_single_one_smul (fun y => cl0 (prod₂ (IrrGL.rep a) (IrrGL.rep y))) b

theorem mulR_sg_left_comm (ha : Assoc k) (hc : Comm k) (a b : IrrGL k) (c : GrothGL k) :
    mulR (sg a) (mulR (sg b) c) = mulR (sg b) (mulR (sg a) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [mulR_sg_zero]
  | add f g hf hg => rw [mulR_sg_add, mulR_sg_add, hf, hg, mulR_sg_add, mulR_sg_add]
  | single z n =>
    have hs : Finsupp.single z n = n • sg z := by simp [sg]
    rw [hs, mulR_sg_zsmul, mulR_sg_zsmul, mulR_sg_zsmul, mulR_sg_zsmul, ← ha a b z, mulR_sg_sg a b,
      hc a b, ← mulR_sg_sg b a, ha b a z]

theorem foldr_perm (ha : Assoc k) (hc : Comm k) {l₁ l₂ : List (IrrGL k)} (p : l₁.Perm l₂) (u : GrothGL k) :
    l₁.foldr (fun y a => mulR (sg y) a) u = l₂.foldr (fun y a => mulR (sg y) a) u := by
  induction p with
  | nil => rfl
  | cons x _ ih => simp only [List.foldr_cons, ih]
  | swap x y l => simp only [List.foldr_cons]; exact mulR_sg_left_comm ha hc y x _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

end Ring

theorem jordan_holder_mult_eq_of_class (y : IrrGL k) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL (Fin y.1) k) V) (π' : Representation ℂ (GL (Fin y.1) k) W)
    (hπ : HasFiniteLength π) (hπ' : HasFiniteLength π') (h : cl0 π = cl0 π') :
    jhMult (IrrGL.rep y) π = jhMult (IrrGL.rep y) π' := by
  have e1 : cl0 π = clsGL π hπ := by unfold cl0; rw [dif_pos hπ]
  have e2 : cl0 π' = clsGL π' hπ' := by unfold cl0; rw [dif_pos hπ']
  have h2 := congrArg (fun a : GrothGL k => a ⟨y.1, y.2⟩) (e1.symm.trans (h.trans e2))
  simp only [clsGL_apply, cls_apply] at h2
  have h3 : (jhMult (IrrGL.rep y) π).toNat = (jhMult (IrrGL.rep y) π').toNat := by exact_mod_cast h2
  rw [← ENat.natCast_toNat (jhMult_ne_top y.2.rep.irr hπ), ← ENat.natCast_toNat (jhMult_ne_top y.2.rep.irr hπ'), h3]

theorem jhMult_mul_jm_le {g N : ℕ} (z : Fin g → IrrGL k) (hz : ∑ b, (z b).1 = N) {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V)
    (τ : Representation ℂ (GL (Fin N) k) W) (hπ : IsSmooth π) :
    jhMult τ π * jm z hz τ ≤ jm z hz π := by
  have hadd : ∀ S T : Subrepresentation π, T ≤ S →
      jm z hz T.toRepresentation + jm z hz (subQuot S T) ≤ jm z hz S.toRepresentation := by
    intro S T h
    let ι : T.toRepresentation.IntertwiningMap S.toRepresentation := ⟨Submodule.inclusion h, fun _ => rfl⟩
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    have hS : IsSmooth S.toRepresentation :=
      (IsSubquotient.of_injective (⟨S.toSubmodule.subtype, fun _ => rfl⟩ :
        S.toRepresentation.IntertwiningMap π) Subtype.val_injective).isSmooth hπ
    refine GlobalTheory.CompanionTheory.CsStages.jhMult_add_le (jacMap _ ι) (jacMap _ p)
      (GlobalTheory.JacquetExact.jacMap_injective _ hS ι (Submodule.inclusion_injective h))
      (GlobalTheory.JacquetExact.jacMap_surjective _ p (Submodule.Quotient.mk_surjective _)) fun u => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have : p (ι v) = 0 := (Submodule.Quotient.mk_eq_zero _).2 v.2
    show Submodule.Quotient.mk (p (ι v)) = 0
    rw [this]
    rfl
  have h := GlobalTheory.CompanionTheory.CsStages.jhMult_mul_le_of_steps τ π (fun S => jm z hz S.toRepresentation) (jm z hz τ)
    (fun S T h => le_trans le_self_add (hadd S T h))
    (fun S T h ⟨φ⟩ => by
      have := hadd S T h
      rwa [GlobalTheory.T.jacquet_multiplicity_of_equiv z hz _ _ ⟨φ⟩] at this)
  rwa [GlobalTheory.T.jacquet_multiplicity_of_equiv z hz _ _ ⟨topEquiv π⟩] at h

theorem ofFn_perm {α : Type*} {h : ℕ} (x : Fin h → α) (σ : Equiv.Perm (Fin h)) :
    (List.ofFn (x ∘ σ)).Perm (List.ofFn x) := by
  exact Equiv.Perm.ofFn_comp_perm σ x

theorem jhMult_le_one_of_equiv (y : IrrGL k) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin y.1) k) V} {g : ℕ} {z : Fin g → IrrGL k} {hz : ∑ b, (z b).1 = y.1}
    (hsoc : IsSocle (IrrGL.rep y) π) (e : π.Equiv (prodIrr z hz)) (hjm : jm z hz (prodIrr z hz) ≤ 1) :
    jhMult (IrrGL.rep y) π ≤ 1 := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨hirr, f, hf, -⟩ := hsoc
  have hnt := nontrivial_of_irreducible hirr
  obtain ⟨v, hv⟩ := exists_ne (0 : y.2.rep.V)
  have hpos : 1 ≤ jm z hz (IrrGL.rep y) :=
    GlobalTheory.T.jacquet_multiplicity_pos hA z hz (IrrGL.rep y) y.2.rep.smooth (e.toIntertwiningMap.comp f)
      ⟨v, fun h0 => hv (hf (e.injective (by simpa using h0)))⟩
  have hle := jhMult_mul_jm_le z hz (prodIrr z hz) (IrrGL.rep y) (isSmooth_prodIrr z hz)
  rw [jhMult_congr_right _ e]
  exact (le_mul_of_one_le_right' hpos).trans (hle.trans hjm)

theorem jhMult_rev_le_one (c : Cls k) (_𝔪 : Multiset (Segment k)) {h : ℕ} (x : Fin h → IrrGL k) (y : IrrGL k)
    (Δ : Fin h → Segment k) (hΔo : ∀ i j, i < j → ¬ (Δ i).Precedes (Δ j)) (hΔL : ∀ i, IsLSeg (Δ i) (x i).rep)
    (hdr : ∑ a, (x (Fin.rev a)).1 = y.1) (hsoc : IsSocle (IrrGL.rep y) (prodIrr (x ∘ Fin.rev) hdr)) :
    jhMult (IrrGL.rep y) (prodIrr (x ∘ Fin.rev) hdr) ≤ 1 := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hΓ : IsRevOrdered (Δ ∘ Fin.rev) := fun i j hij => hΔo (Fin.rev j) (Fin.rev i) (Fin.rev_lt_rev.2 hij)
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_canonical_segment_order (Δ ∘ Fin.rev)
  have hσr := GlobalTheory.T.canonical_segments_reverse_ordered _ hσ
  have hdrs : ∑ a, ((x ∘ Fin.rev) (σ a)).1 = y.1 := by
    rw [← hdr]; exact Equiv.sum_comp σ (fun a => ((x ∘ Fin.rev) a).1)
  obtain ⟨e1⟩ := GlobalTheory.T.reverse_ordered_product_perm_equiv hA c.com (Δ ∘ Fin.rev) σ (x ∘ Fin.rev) hdr hdrs hΓ hσr (fun i => hΔL (Fin.rev i))
  obtain ⟨g, z, hz, ⟨e2⟩, hjm⟩ :=
    GlobalTheory.T.canonical_product_equiv_multiplicity_one hA c.jac c.unl ((Δ ∘ Fin.rev) ∘ σ) ((x ∘ Fin.rev) ∘ σ) hdrs hσ (fun i => hΔL (Fin.rev (σ i)))
  have e : (prodIrr (x ∘ Fin.rev) hdr).Equiv (prodIrr z hz) := e1.trans e2
  exact jhMult_le_one_of_equiv y hsoc e hjm

end GrothendieckSingleMultiplication

open GrothendieckSingleMultiplication in
variable (k) in
theorem multOne (c : Cls k) (_hm : MulCls k) (ha : Assoc k) (hc : Comm k) (_h1 : One k) (hl : ProdList k) :
    MultOne k := by
  intro 𝔪 h x y hd hx hy
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨Δ, ⟨hΔm, hΔo⟩, hΔL⟩ := hx
  have hdr : ∑ a, (x (Fin.rev a)).1 = y.1 := by
    rw [← hd]; exact Equiv.sum_comp Fin.revPerm (fun a => (x a).1)
  have hsoc : IsSocle (IrrGL.rep y) (prodIrr (x ∘ Fin.rev) hdr) :=
    by have hs := c.soc; unfold LSocleGL at hs; exact hs 𝔪 h y.1 x hdr ⟨Δ, ⟨hΔm, hΔo⟩, hΔL⟩ (IrrGL.rep y) hy
  have hcl : cl0 (prodIrr x hd) = cl0 (prodIrr (x ∘ Fin.rev) hdr) := by
    rw [hl h y.1 x hd, hl h y.1 (x ∘ Fin.rev) hdr]
    exact foldr_perm ha hc (ofFn_perm x Fin.revPerm).symm _
  rw [jordan_holder_mult_eq_of_class y _ _ (GlobalTheory.T.product_irreducible_finite_length hA x hd) (GlobalTheory.T.product_irreducible_finite_length hA (x ∘ Fin.rev) hdr) hcl]
  exact le_antisymm (jhMult_rev_le_one c 𝔪 x y Δ hΔo hΔL hdr hsoc)
    (Order.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 hsoc.isSubquotient))

end CompanionTheory.Groth
end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth.JClsPf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem piTensor_irr {h : ℕ} (x : Fin h → IrrGL k) : (piTensor fun a => (x a).rep).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) fun a φ hφ =>
    GlobalTheory.SchurAdm.schur_admissible _ (KO k (Fin (x a).1)) GlobalTheory.SplitFlip.isOpen_KO
      GlobalTheory.SplitFlip.isCompact_KO _ _ (x a).2.rep.irr
      (CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k _ _ _ (x a).2.rep.smooth (x a).2.rep.irr) φ hφ

theorem jm_ne_top {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsSmooth π) (hl : HasFiniteLength π) : jm x hd π ≠ ⊤ :=
  jhMult_ne_top (piTensor_irr x)
    (GlobalTheory.T.jacquet_module_finite_length k (Fin h) (Fin N) (fun a => Fin (x a).1) (stdBlocks (fun a => (x a).1) hd) V π hπ hl)

theorem jm_congr {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W}
    (hπ : IsSmooth π) (hτ : IsSmooth τ) (φ : π.Equiv τ) : jm x hd π = jm x hd τ :=
  le_antisymm (GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient x hd π τ hτ (.of_injective φ.toIntertwiningMap φ.injective))
    (GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient x hd τ π hπ (.of_surjective φ.toIntertwiningMap φ.surjective))

theorem jm_eq_sum {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsSmooth π) (hl : HasFiniteLength π) :
    jm x hd π = ∑ c ∈ (finite_constituents hl).toFinset, jhMult c.rep.ρ π * jm x hd c.rep.ρ := by
  set F := (finite_constituents hl).toFinset with hF
  have hσ := piTensor_irr x
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := π)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hl
  have : WellFoundedGT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedLT
  have key : ∀ S : Subrepresentation π,
      jm x hd S.toRepresentation = ∑ c ∈ F, jhMult c.rep.ρ S.toRepresentation * jm x hd c.rep.ρ := by
    intro S
    induction S using WellFoundedLT.induction with
    | ind S ih =>
    rcases eq_or_ne S ⊥ with rfl | hne
    · have h0 : Subsingleton (⊥ : Subrepresentation π).toSubmodule :=
        inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
      have h1 : Subsingleton (Jacquet (⊥ : Subrepresentation π).toRepresentation
          (unipRad k (stdBlocks (fun a => (x a).1) hd))) :=
        (Submodule.Quotient.mk_surjective _).subsingleton
      rw [jm, jhMult_of_subsingleton hσ]
      refine (Finset.sum_eq_zero fun c _ => ?_).symm
      rw [jhMult_of_subsingleton c.rep.irr, zero_mul]
    obtain ⟨T, -, hT⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hne)
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    let j : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
    have hq : IsSubquotient (subQuot S T) S.toRepresentation :=
      .of_surjective p (Submodule.Quotient.mk_surjective _)
    have hqπ : IsSubquotient (subQuot S T) π := hq.trans (.of_injective j Subtype.val_injective)
    have hsm : IsSmooth (subQuot S T) := hqπ.isSmooth hπ
    have hirr : (subQuot S T).IsIrreducible := isIrreducible_subQuot hT
    let τ : IrrRep (GL (Fin N) k) := ⟨_, subQuot S T, hsm, hirr⟩
    have hsplit : jm x hd S.toRepresentation = jm x hd T.toRepresentation + jm x hd (subQuot S T) :=
      GlobalTheory.CompanionTheory.WordIrr.jhMult_jac_of_le _ hσ hπ hT.le
    have hmult : ∀ c : IrrCl (GL (Fin N) k), jhMult c.rep.ρ S.toRepresentation =
        jhMult c.rep.ρ T.toRepresentation + jhMult c.rep.ρ (subQuot S T) :=
      fun c => jhMult_of_le c.rep.irr hT.le
    have hzero : ∀ c : IrrCl (GL (Fin N) k), c ≠ τ.cl → jhMult c.rep.ρ (subQuot S T) = 0 := by
      intro c hc
      by_contra h0
      obtain ⟨ψ⟩ := (jhMult_ne_zero_iff.1 h0).nonempty_equiv c.rep.irr hirr
      exact hc (c.cl_rep.symm.trans (IrrRep.cl_eq_iff.2 ⟨ψ.symm⟩))
    obtain ⟨ψ⟩ := τ.nonempty_equiv_rep
    have hone : jhMult τ.cl.rep.ρ (subQuot S T) = 1 := by
      rw [jhMult_congr_left ψ]
      exact jhMult_self hirr
    have hmem : τ.cl ∈ F := by
      rw [hF, Set.Finite.mem_toFinset]
      intro h0
      have := GlobalTheory.CompanionTheory.JmMono.jhMult_le_of_isSubquotient τ.cl.rep.ρ hqπ
      rw [hone, h0] at this
      exact absurd this (by simp)
    have hQ : jm x hd (subQuot S T) = ∑ c ∈ F, jhMult c.rep.ρ (subQuot S T) * jm x hd c.rep.ρ := by
      rw [Finset.sum_eq_single_of_mem τ.cl hmem (fun c _ hc => by rw [hzero c hc, zero_mul]), hone, one_mul]
      exact (jm_congr x hd τ.cl.rep.smooth hsm ψ).symm
    rw [hsplit, ih T hT.lt, hQ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hmult c, add_mul]
  have hT1 : IsSmooth (⊤ : Subrepresentation π).toRepresentation :=
    (IsSubquotient.of_injective (topEquiv π).toIntertwiningMap (topEquiv π).injective).isSmooth hπ
  rw [← jm_congr x hd hT1 hπ (topEquiv π), key ⊤]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [jhMult_congr_right _ (topEquiv π)]

end CompanionTheory.Groth.JClsPf

namespace CompanionTheory.Groth

open CompanionTheory.Groth.JClsPf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem jacquet_functional_class (W : List (IrrGL k)) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hl : HasFiniteLength π) :
    J W (cl0 π) = (cls π hl).sum fun c m => m * ((jmL W (IrrGL.rep (⟨N, c⟩ : IrrGL k))).toNat : ℤ) := by
  unfold J cl0
  rw [dif_pos hl, clsGL, Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]

variable (k) in

theorem jCls : JCls k := by
  intro W N V _ _ π hπ hl
  by_cases hd : ∑ a, (W.get a).1 = N
  · have hjπ : jmL W π = jm W.get hd π := dif_pos hd
    have hjc : ∀ c : IrrCl (GL (Fin N) k), jmL W (IrrGL.rep (⟨N, c⟩ : IrrGL k)) = jm W.get hd c.rep.ρ :=
      fun c => dif_pos hd
    refine ⟨by rw [hjπ]; exact jm_ne_top W.get hd π hπ hl, ?_⟩
    set F := (finite_constituents hl).toFinset with hF
    have ha : ∀ c : IrrCl (GL (Fin N) k), jhMult c.rep.ρ π ≠ ⊤ := fun c => jhMult_ne_top c.rep.irr hl
    have hb : ∀ c : IrrCl (GL (Fin N) k), jm W.get hd c.rep.ρ ≠ ⊤ :=
      fun c => jm_ne_top W.get hd c.rep.ρ c.rep.smooth c.rep.hasFiniteLength
    have hsum : jm W.get hd π =
        ((∑ c ∈ F, (jhMult c.rep.ρ π).toNat * (jm W.get hd c.rep.ρ).toNat : ℕ) : ℕ∞) := by
      rw [jm_eq_sum W.get hd π hπ hl, Nat.cast_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Nat.cast_mul, ENat.natCast_toNat (ha c), ENat.natCast_toNat (hb c)]
    have hsub : (cls π hl).support ⊆ F := by
      intro c hc
      rw [Finsupp.mem_support_iff, cls_apply] at hc
      rw [hF, Set.Finite.mem_toFinset]
      intro h0
      exact hc (by rw [h0]; rfl)
    rw [jacquet_functional_class W π hl, hjπ, hsum, ENat.toNat_natCast, Nat.cast_sum,
      Finsupp.sum_of_support_subset (cls π hl) hsub
        (fun c m => m * ((jmL W (IrrGL.rep (⟨N, c⟩ : IrrGL k))).toNat : ℤ)) (fun c _ => zero_mul _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hjc c, cls_apply, Nat.cast_mul]
  · have hjπ : jmL W π = 0 := dif_neg hd
    have hjc : ∀ c : IrrCl (GL (Fin N) k), jmL W (IrrGL.rep (⟨N, c⟩ : IrrGL k)) = 0 := fun c => dif_neg hd
    refine ⟨by rw [hjπ]; exact ENat.zero_ne_top, ?_⟩
    rw [jacquet_functional_class W π hl, hjπ]
    simp [hjc, Finsupp.sum]

end CompanionTheory.Groth

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace SegJ

open Classical in

theorem jhMult_seg_cl (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) (Δ : Segment k)
    (y : Fin Δ.len → IrrCl (GL (Fin Δ.d) k)) (hd : ∑ _ : Fin Δ.len, Δ.d = Δ.len * Δ.d) :
    jhMult (piTensor fun a => (y a).rep.ρ) (jac (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (Z Δ).rep.ρ) =
      if (∀ a, (⟨Δ.d, y a⟩ : IrrGL k) = Δ.term a) then 1 else 0 := by
  obtain ⟨Φ⟩ := ((hZ Δ Δ.start.rep Δ.start.cl_rep (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (Z Δ).rep).2).1
    (Z Δ).cl_rep
  let Ψ : (piTensor (segTerm Δ.start.rep.ρ Δ.len)).Equiv (piTensor fun a => (Δ.term a).rep) :=
    piTensorEquiv fun _ => Δ.first.twEquiv _ (isSmoothChar_absPow _)
  have hT : (piTensor fun a => (Δ.term a).rep).IsIrreducible :=
    GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA Δ.term
  rw [jhMult_congr_right _ (Φ.trans Ψ)]
  split_ifs with h
  · have hy : ∀ a, y a = (Δ.term a).2 := fun a => eq_of_heq (Sigma.mk.inj_iff.1 (h a)).2
    obtain rfl : y = fun a => (Δ.term a).2 := funext hy
    exact jhMult_self hT
  · by_contra hne
    have hy : (piTensor fun a => (y a).rep.ρ).IsIrreducible :=
      GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (fun a => (⟨Δ.d, y a⟩ : IrrGL k))
    obtain ⟨φ⟩ := GlobalTheory.LocGL.SupportUnique.nonempty_equiv_of_isSubquotient hy hT (jhMult_ne_zero_iff.1 hne)
    have hcl := GlobalTheory.T.tensor_product_determines_factor_classes (Fin Δ.len) (fun _ => GL (Fin Δ.d) k) (fun a => (Δ.term a).2.rep)
      (fun a => (y a).rep) ⟨φ⟩
    refine h fun a => ?_
    have h1 : (Δ.term a).2 = y a := (IrrCl.cl_rep _).symm.trans ((hcl a).trans (IrrCl.cl_rep _))
    rw [← h1]
    rfl

open Classical in

theorem jm_seg (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) (Δ : Segment k)
    {m : ℕ} (y : Fin m → IrrGL k) (hy : ∀ a, (y a).1 = Δ.d) (hd : ∑ a, (y a).1 = Δ.len * Δ.d) :
    jm y hd (IrrGL.rep (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL k)) =
      if ∃ h : m = Δ.len, ∀ a, y a = Δ.term (Fin.cast h a) then 1 else 0 := by
  have hm : m = Δ.len := by
    have h1 : ∑ a, (y a).1 = m * Δ.d := by simp [hy]
    exact Nat.eq_of_mul_eq_mul_right Δ.d_pos (h1.symm.trans hd)
  subst hm
  obtain ⟨y', rfl⟩ : ∃ y' : Fin Δ.len → IrrCl (GL (Fin Δ.d) k), y = fun a => ⟨Δ.d, y' a⟩ :=
    ⟨fun a => cast (congrArg (fun n => IrrCl (GL (Fin n) k)) (hy a)) (y a).2,
      funext fun a => Sigma.ext (hy a) (cast_heq _ _).symm⟩
  show jhMult (piTensor fun a => (y' a).rep.ρ) (jac (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (Z Δ).rep.ρ) = _
  rw [jhMult_seg_cl hA hZ Δ y' hd]
  congr 1
  exact propext ⟨fun h => ⟨rfl, fun a => by simpa using h a⟩, fun ⟨_, h⟩ a => by simpa using h a⟩

open Classical in

theorem jmL_seg (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) (Δ : Segment k)
    (W : List (IrrGL k)) (hW : ∀ w ∈ W, w.1 = Δ.d) (hl : W.length = Δ.len) :
    jmL W (IrrGL.rep (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL k)) = if W = List.ofFn Δ.term then 1 else 0 := by
  have hy : ∀ a, (W.get a).1 = Δ.d := fun a => hW _ (List.get_mem _ _)
  have hd : ∑ a, (W.get a).1 = Δ.len * Δ.d := by
    rw [Finset.sum_congr rfl fun a _ => hy a]
    simp [hl]
  unfold jmL
  rw [dif_pos hd, jm_seg hA hZ Δ W.get hy hd]
  congr 1
  refine propext ⟨fun ⟨h, h2⟩ => ?_, ?_⟩
  · refine List.ext_get (by simp [h]) fun n h1 h3 => ?_
    simpa using h2 ⟨n, h1⟩
  · rintro rfl
    exact ⟨List.length_ofFn, fun a => by simp; rfl⟩

theorem vWord_ne (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (S : Finset (Fin Δ.len))
    (hS : S ∈ vSets Δ) (hne : S ≠ ∅) : vWord Δ S ≠ List.ofFn Δ.term := by
  intro H
  rw [vWord, List.ofFn_eq_map] at H
  have H2 := (List.map_injective_iff.2 (GlobalTheory.T.segment_term_injective hA Δ)) H
  obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have hL1 : ((List.finRange Δ.len).filter fun a => a ∈ S) ≠ [] :=
    List.ne_nil_of_mem (List.mem_filter.2 ⟨List.mem_finRange s, by simpa using hs⟩)
  obtain ⟨x, t, hxt⟩ := List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.2 hL1)
  have hx : x ∈ S := by
    have : x ∈ ((List.finRange Δ.len).filter fun a => a ∈ S).reverse := hxt ▸ List.mem_cons_self ..
    simpa using this
  rw [hxt] at H2
  have h0 := congrArg (fun L => L[0]?) H2
  simp at h0
  have h3 := (Finset.mem_filter.1 hS).2 x hx
  rw [List.getElem?_eq_getElem (by simpa using Δ.len_pos)] at h0
  have h4 := Option.some.inj h0
  apply h3
  rw [h4]
  simp

end SegJ

open SegJ in
variable (k) in

theorem jSeg : JSeg k := by
  intro Z hZ Δ
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hterm : ∀ a, (Δ.term a).1 = Δ.d := fun _ => rfl
  refine ⟨?_, fun S hS hne => ?_⟩
  · rw [jmL_seg hA hZ Δ _ (fun w hw => by rw [List.mem_ofFn] at hw; obtain ⟨a, rfl⟩ := hw; rfl) List.length_ofFn, if_pos rfl]
  · rw [jmL_seg hA hZ Δ _ ?_ ?_, if_neg (vWord_ne hA Δ S hS hne)]
    · intro w hw
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw
      rfl
    · simp [vWord]
      rw [← List.length_eq_length_filter_add]
      simp

end CompanionTheory.Groth

end
end

section
open MvPolynomial

namespace CompanionTheory.Groth.ChartWirtingerDerivatives

def toZAlg {σ : Type*} (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ) :
    MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial σ ℤ :=
  AlgHom.mk ψ (by
    intro r
    show ψ (algebraMap ℤ (MvPolynomial σ ℤ) r) = algebraMap ℤ (MvPolynomial σ ℤ) r
    rw [algebraMap_eq, eq_intCast C r]
    exact map_intCast ψ r)

theorem tri_supported_le {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) (N : ℕ) :
    supported ℤ {t | w t < N} ≤ (supported ℤ {t | w t < N}).map (toZAlg ψ) := by
  induction N with
  | zero =>
    rw [supported_eq_adjoin_X, Algebra.adjoin_le_iff]
    rintro _ ⟨t, ht, rfl⟩
    exact absurd ht (by simp)
  | succ N ih =>
    rw [supported_eq_adjoin_X, Algebra.adjoin_le_iff]
    rintro _ ⟨t, ht, rfl⟩
    simp only [Set.mem_ofPred_eq] at ht
    have hmono : (supported ℤ {t | w t < N}).map (toZAlg ψ) ≤
        (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) :=
      Subalgebra.map_mono (supported_mono fun t (ht : w t < N) => (Nat.lt_succ_of_lt ht : w t < N + 1))
    obtain ⟨ε, p, hp, hψ⟩ := h t
    have hpmem : p ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) := by
      apply hmono; apply ih
      rw [mem_supported]
      intro u hu
      have := hp u hu
      simp only [Set.mem_ofPred_eq]; omega
    have hXmem : ψ (X t) ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) :=
      Subalgebra.mem_map.2 ⟨X t, (X_mem_supported).2 (by simpa using ht), rfl⟩
    have heq : (X t : MvPolynomial σ ℤ) = (ε : ℤ) • ψ (X t) - (ε : ℤ) • p := by
      rw [hψ, smul_add, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul, add_sub_cancel_right]
    rw [SetLike.mem_coe, heq]
    exact Subalgebra.sub_mem _ (Subalgebra.smul_mem _ hXmem _) (Subalgebra.smul_mem _ hpmem _)

theorem tri_surj {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) : Function.Surjective ψ := by
  intro y
  have hy : y ∈ supported ℤ {t | w t < y.vars.sup (fun t => w t + 1)} := by
    rw [mem_supported]
    intro t ht
    have := Finset.le_sup (f := fun t => w t + 1) (Finset.mem_coe.1 ht)
    simp only [Set.mem_ofPred_eq]; omega
  obtain ⟨x, -, hx⟩ := Subalgebra.mem_map.1 (tri_supported_le w ψ h _ hy)
  exact ⟨x, hx⟩

theorem tri_bij {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) : Function.Bijective ψ := by
  refine ⟨?_, tri_surj w ψ h⟩
  choose ε p hp hψ using h
  have hq : ∀ s, ∃ q : MvPolynomial σ ℤ, (∀ t ∈ q.vars, w t < w s) ∧ ψ q = -((ε s : ℤ) • p s) := by
    intro s
    have hmem : -((ε s : ℤ) • p s) ∈ supported ℤ {t | w t < w s} :=
      neg_mem (Subalgebra.smul_mem _ (mem_supported.2 fun t ht => hp s t ht) _)
    obtain ⟨q, hq, hq'⟩ := Subalgebra.mem_map.1
      (tri_supported_le w ψ (fun s => ⟨ε s, p s, hp s, hψ s⟩) (w s) hmem)
    exact ⟨q, fun t ht => mem_supported.1 hq ht, hq'⟩
  choose q hqv hqψ using hq
  let g : σ → MvPolynomial σ ℤ := fun s => (ε s : ℤ) • X s + q s
  let φ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ := (aeval g : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial σ ℤ).toRingHom
  have hφX : ∀ s, φ (X s) = (ε s : ℤ) • X s + q s := fun s => aeval_X g s
  have hcomp : ∀ x, ψ (φ x) = x := by
    have hAlg : (toZAlg ψ).comp (aeval g) = AlgHom.id ℤ (MvPolynomial σ ℤ) := by
      apply MvPolynomial.algHom_ext
      intro s
      show ψ (φ (X s)) = X s
      rw [hφX, map_add, map_zsmul, hψ, hqψ, smul_add, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul,
        add_neg_cancel_right]
    intro x
    exact AlgHom.congr_fun hAlg x
  have hφs : Function.Surjective φ := tri_surj w φ fun s => ⟨ε s, q s, hqv s, hφX s⟩
  intro x y hxy
  obtain ⟨a, rfl⟩ := hφs x
  obtain ⟨b, rfl⟩ := hφs y
  have hab : a = b := (hcomp a).symm.trans (hxy.trans (hcomp b))
  rw [hab]

theorem uni_inj {M I : Type*} (L : M ≃ I) (w : M → ℕ) (f : M → I →₀ ℤ)
    (h1 : ∀ m, f m (L m) = 1) (hlt : ∀ m n, f m (L n) ≠ 0 → m = n ∨ w m < w n) :
    Function.Injective (Finsupp.linearCombination ℤ f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  by_contra hne
  obtain ⟨m0, hm0, hmin⟩ := a.support.exists_min_image w (Finsupp.support_nonempty_iff.2 hne)
  have hval := congrArg (fun y : I →₀ ℤ => y (L m0)) ha
  simp only [Finsupp.linearCombination_apply, Finsupp.coe_zero, Pi.zero_apply] at hval
  rw [Finsupp.sum_apply, Finsupp.sum, Finset.sum_eq_single m0] at hval
  · simp only [Finsupp.smul_apply, h1, smul_eq_mul, mul_one] at hval
    exact (Finsupp.mem_support_iff.1 hm0) hval
  · intro m hm hne'
    simp only [Finsupp.smul_apply, smul_eq_mul]
    by_cases hf : f m (L m0) = 0
    · simp [hf]
    · rcases hlt m m0 hf with h | h
      · exact absurd h hne'
      · exact absurd (hmin m hm) (not_le.2 h)
  · intro h; exact absurd hm0 h

theorem uni_exists {M I C : Type*} (L : M ≃ I) (c : M → C) (w : M → ℕ) (b : C → ℕ) (f : M → I →₀ ℤ)
    (hb : ∀ m, w m ≤ b (c m)) (h1 : ∀ m, f m (L m) = 1)
    (hlt : ∀ m n, f m (L n) ≠ 0 → c m = c n ∧ (m = n ∨ w m < w n)) :
    ∀ n, ∃ a : M →₀ ℤ, (∀ m ∈ a.support, c m = c n) ∧
      Finsupp.linearCombination ℤ f a = Finsupp.single (L n) 1 := by
  classical
  suffices H : ∀ d n, b (c n) - w n ≤ d → ∃ a : M →₀ ℤ, a ∈ Finsupp.supported ℤ ℤ {m | c m = c n} ∧
      Finsupp.linearCombination ℤ f a = Finsupp.single (L n) 1 by
    intro n
    obtain ⟨a, ha, ha'⟩ := H _ n le_rfl
    exact ⟨a, fun m hm => (Finsupp.mem_supported _ _).1 ha hm, ha'⟩
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro n hn
  have H : ∀ i ∈ (f n).support.erase (L n), ∃ a : M →₀ ℤ,
      a ∈ Finsupp.supported ℤ ℤ {m | c m = c n} ∧
      Finsupp.linearCombination ℤ f a = Finsupp.single i 1 := by
    intro i hi
    obtain ⟨hne, hi⟩ := Finset.mem_erase.1 hi
    have hf : f n (L (L.symm i)) ≠ 0 := by
      rw [L.apply_symm_apply]; exact Finsupp.mem_support_iff.1 hi
    obtain ⟨hc, hw⟩ := hlt n (L.symm i) hf
    have hw' : w n < w (L.symm i) :=
      hw.resolve_left fun h => hne (by rw [h, L.apply_symm_apply])
    have hb' := hb (L.symm i)
    have hlt' : b (c (L.symm i)) - w (L.symm i) < d := by
      rw [hc] at hn; omega
    obtain ⟨a, ha, ha'⟩ := ih _ hlt' (L.symm i) le_rfl
    refine ⟨a, ?_, by rw [ha', L.apply_symm_apply]⟩
    rwa [hc]
  choose! g hg hg' using H
  refine ⟨Finsupp.single n 1 - ∑ i ∈ (f n).support.erase (L n), f n i • g i, ?_, ?_⟩
  · exact Submodule.sub_mem _ (Finsupp.single_mem_supported ℤ _ rfl)
      (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (hg i hi))
  · have hs : ∑ i ∈ (f n).support.erase (L n), Finsupp.linearCombination ℤ f (f n i • g i) =
        ∑ i ∈ (f n).support.erase (L n), f n i • Finsupp.single i (1 : ℤ) :=
      Finset.sum_congr rfl fun i hi => by rw [map_smul, hg' i hi]
    have hsplit : f n = Finsupp.single (L n) 1 +
        ∑ i ∈ (f n).support.erase (L n), f n i • Finsupp.single i (1 : ℤ) := by
      conv_lhs => rw [← Finsupp.sum_single (f n)]
      rw [Finsupp.sum, ← Finset.add_sum_erase _ _
        (Finsupp.mem_support_iff.2 (by rw [h1]; exact one_ne_zero)), h1]
      simp_rw [Finsupp.smul_single_one]
    rw [map_sub, map_sum, Finsupp.linearCombination_single, one_smul, hs]
    exact (eq_sub_of_add_eq hsplit.symm).symm

theorem uni_bij {M I C : Type*} (L : M ≃ I) (c : M → C) (w : M → ℕ) (b : C → ℕ) (f : M → I →₀ ℤ)
    (hb : ∀ m, w m ≤ b (c m)) (h1 : ∀ m, f m (L m) = 1)
    (hlt : ∀ m n, f m (L n) ≠ 0 → c m = c n ∧ (m = n ∨ w m < w n)) :
    Function.Bijective (Finsupp.linearCombination ℤ f) := by
  refine ⟨uni_inj L w f h1 fun m n h => (hlt m n h).2, ?_⟩
  intro y
  refine Finsupp.induction_linear y ?_ ?_ ?_
  · exact ⟨0, map_zero _⟩
  · rintro y z ⟨a, ha⟩ ⟨a', ha'⟩
    exact ⟨a + a', by rw [map_add, ha, ha']⟩
  · intro i r
    obtain ⟨a, -, ha⟩ := uni_exists L c w b f hb h1 hlt (L.symm i)
    exact ⟨r • a, by rw [map_smul, ha, L.apply_symm_apply, Finsupp.smul_single_one]⟩

end CompanionTheory.Groth.ChartWirtingerDerivatives

namespace CompanionTheory.Groth

theorem triAut : TriAut := fun _ w ψ h => ChartWirtingerDerivatives.tri_bij w ψ h

theorem uniTri : UniTri := fun _ _ _ L c w b f hb h1 hlt =>
  ⟨ChartWirtingerDerivatives.uni_bij L c w b f hb h1 hlt, ChartWirtingerDerivatives.uni_exists L c w b f hb h1 hlt⟩

end CompanionTheory.Groth
end

section
namespace CompanionTheory.Groth

theorem groth_of_cls (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Cls k) :
    GlobalTheory.Published.GrothendieckRingPolynomial := by
  refine groth_of_steps (fun k _ _ _ _ => ?_) triAut uniTri
  have hm : MulCls k := by apply mulCls
  have ha : Assoc k := by apply assoc; exact hm
  have hc : Comm k := comm k
  have h1 : One k := by apply one
  have hl : ProdList k := by apply prodList; exact hm
  refine ⟨H k, hm, ha, hc, h1, hl, tri k (H k), ?_, by apply jCls, by apply jSeg, altSum k⟩
  apply multOne <;> first | exact H k | assumption

end CompanionTheory.Groth
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos CompanionTheory.Exh GlobalTheory.CompanionTheory.ExhGood

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth.ClsOfF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem comm_of (hI : Zc.Cos.LUnlinkedIrr k) : Zc.Cos.LUnlinkedComm k :=
  GlobalTheory.T.unlinked_commute_of_irreducible k CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top hI

theorem stdCos (hZ : GlobalTheory.Published.SegmentRepresentation) (hI : Zc.Cos.LUnlinkedIrr k) :
    ∀ (𝔪 : Multiset (Segment k)) (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x →
      ∃ π : IrrRep (GL (Fin N) k), IsCosocle π.ρ (prodIrr x hd) := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  intro 𝔪 h N x hd hx
  obtain ⟨Γ, hΓ, hL⟩ := GlobalTheory.T.langlands_factors_dual_reverse_ordered hA (GlobalTheory.T.langlands_segment_dual hA hZ) 𝔪 x hx
  obtain ⟨hd', ⟨e⟩⟩ := GlobalTheory.T.contragredient_product_irreducible hA x hd
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.reverse_ordered_product_has_socle hA (GlobalTheory.T.segment_jacquet_all hA hZ) hI (comm_of hI) Γ (fun a => dualCl (x a)) hd' hΓ hL
  exact GlobalTheory.T.cosocle_of_contragredient_socle hA (prodIrr x hd) (isSmooth_prodIrr x hd) (GlobalTheory.T.product_irreducible_finite_length hA x hd) τ
    (hτ.of_equiv (Representation.Equiv.refl _) e.symm)

theorem segCl (Δ : Segment k) : ∃ x : IrrGL k, IsLSeg Δ x.rep := by
  obtain ⟨π, hπ⟩ := GlobalTheory.T.exists_segment_representation CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top Δ
  exact ⟨IrrGL.of π.ρ π.smooth π.irr, hπ.of_equiv (IrrGL.equivOf π.ρ π.smooth π.irr)⟩

theorem ex_of (HS : ∀ (𝔪 : Multiset (Segment k)) (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x →
      ∃ π : IrrRep (GL (Fin N) k), IsCosocle π.ρ (prodIrr x hd)) (𝔪 : Multiset (Segment k)) :
    ∃ x : IrrGL k, IsL 𝔪 x.rep := by
  obtain ⟨Δ, hΔ⟩ := GlobalTheory.LocGL.exists_isOrderedForm 𝔪
  choose y hy using (segCl (k := k))
  let x : Fin 𝔪.card → IrrGL k := fun i => y (Δ i)
  have hx : LFactors 𝔪 x := ⟨Δ, hΔ, fun i => hy (Δ i)⟩
  obtain ⟨π, hπ⟩ := HS 𝔪 𝔪.card _ x rfl hx
  refine ⟨IrrGL.of π.ρ π.smooth π.irr, 𝔪.card, x, rfl, hx, ?_⟩
  exact hπ.of_equiv (IrrGL.equivOf π.ρ π.smooth π.irr) (.refl _)

theorem peelGood (HS : ∀ (𝔪 : Multiset (Segment k)) (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x →
      ∃ π : IrrRep (GL (Fin N) k), IsCosocle π.ρ (prodIrr x hd)) (HL : LSocleGL k) : Zc.PeelGoodP k := by
  intro x y hd s 𝔫 hs hn hf hp
  obtain ⟨f, hf⟩ := hf
  have hn' := hn
  obtain ⟨h, z, hz, ⟨Δ, hΔ, hzL⟩, -⟩ := hn'
  let w : Fin (h + 1) → IrrGL k := Fin.snoc (α := fun _ => IrrGL k) z (y 0)
  have hwL : LFactors (𝔫 + {s}) w := by
    refine ⟨_, isOrderedForm_snoc hΔ s hp, fun i => ?_⟩
    induction i using Fin.lastCases with
    | last =>
      have e : w (Fin.last h) = y 0 := Fin.snoc_last (α := fun _ => IrrGL k) _ _
      rw [e, Fin.snoc_last]
      exact hs
    | cast i =>
      have e : w i.castSucc = z i := Fin.snoc_castSucc (α := fun _ => IrrGL k) _ _ _
      rw [e, Fin.snoc_castSucc]
      exact hzL i
  have hwd : ∑ a, (w a).1 = x.1 := by
    rw [Fin.sum_univ_castSucc, ← hd, Fin.sum_univ_two, add_comm, ← hz]
    simp [w]
  have hwr : ∑ a, (w (Fin.rev a)).1 = x.1 := (Equiv.sum_comp Fin.revPerm fun a => (w a).1).trans hwd
  have hzr : ∑ a, (z (Fin.rev a)).1 = (y 1).1 := (Equiv.sum_comp Fin.revPerm fun a => (z a).1).trans hz
  obtain ⟨π, hπ⟩ := HS (𝔫 + {s}) (h + 1) x.1 w hwd hwL
  have hπL : IsL (𝔫 + {s}) π.ρ := ⟨_, w, hwd, hwL, hπ⟩
  have hsoc := HL (𝔫 + {s}) (h + 1) x.1 w hwr hwL π.ρ hπL
  have hsoc₁ := HL 𝔫 h (y 1).1 z hzr ⟨Δ, hΔ, hzL⟩ (y 1).rep hn
  obtain ⟨-, g, hg, -⟩ := hsoc₁
  obtain ⟨F, hF⟩ := embed_family y (w ∘ Fin.rev) (z ∘ Fin.rev)
    (by simp [w, Function.comp]) (fun i => by simp [w, Function.comp, Fin.rev_succ]) hd hwr hzr g hg
  obtain ⟨e⟩ := hsoc.equiv_of_embeds x.2.rep.irr ⟨F.comp f, hF.comp hf⟩
  exact hπL.of_equiv e.symm

theorem exh_at (hM : MidP k) (hR : RefineP k) (hS : SwapP k) (hC : CuspEmbP k) (hP : SuppP k) (hJ : JuxtP k)
    (hL : LinkP k) (hm : MinP k) (hG : Zc.PeelGoodP k) (x : IrrGL k) : ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep := by
  suffices H : ∀ n : ℕ, ∀ x : IrrGL k, x.1 = n → ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep from H _ x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exact GlobalTheory.LocGL.exh_le_one x (by omega)
    obtain ⟨l, hl, hx⟩ := hC x
    have hne : l ≠ [] := by
      rintro rfl
      obtain ⟨hd, -⟩ := hx
      simp at hd
      omega
    obtain ⟨ρ, hρ, hmin⟩ := hm l hne hl
    obtain ⟨A, B, rfl⟩ := List.append_of_mem hρ
    obtain ⟨Γ, c, y, e, hc, hy⟩ := move_left hM hR hS hJ hL x ρ A
      (fun a ha => ⟨hl a (List.mem_append_left _ ha), by simpa using hmin a (List.mem_append_left _ ha) 1 one_pos⟩)
      (Segment.single ρ (hl ρ hρ)) ρ B rfl (single_spec (hl ρ hρ)).2.1 (by simpa using hx)
    obtain ⟨hd, f, hf⟩ := id hy
    have hdeg : Γ.deg = c.1 := hc.deg_eq
    have hpos' : 0 < Γ.deg := Nat.mul_pos Γ.len_pos Γ.d_pos
    have hd2 : c.1 + y.1 = x.1 := (Fin.sum_univ_two fun a => ([c, y].get a).1).symm.trans hd
    obtain ⟨𝔫, h𝔫⟩ := ih y.1 (by omega) y rfl
    refine ⟨_, hG x [c, y].get hd Γ 𝔫 hc h𝔫 ⟨f, hf⟩ fun Δ' hΔ' hp => ?_⟩
    obtain ⟨j, hj, ej⟩ := hp.2
    exact hmin _ (hP x c y _ 𝔫 hl hx hy h𝔫 Δ' hΔ') j hj (e.symm.trans ej)

end CompanionTheory.Groth.ClsOfF

namespace CompanionTheory.Groth

open ClsOfF in

theorem cls_of (hZ : GlobalTheory.Published.SegmentRepresentation) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hI : Zc.Cos.LUnlinkedIrr k)
    (H : CompanionTheory.Exh.MidP k ∧ CompanionTheory.Exh.RefineP k ∧ CompanionTheory.Exh.SwapP k) : Cls k := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨hM, hR, hS⟩ := H
  have hCm : Zc.Cos.LUnlinkedComm k := comm_of hI
  have hF : Zc.LOrderFree k := CompanionTheory.PfEss.Zc2.cs_orderfree hA hCm
  have hSoc : Zc.LSocleGL k := GlobalTheory.T.langlands_socle_of_order_free hA (GlobalTheory.T.local_langlands_of_irreducible_admissible hA) hF
  have HS := stdCos hZ hI
  have hC : CuspEmbP k := cuspEmbP k hA hR
  exact
    { ex := ex_of HS
      exh := exh_at hM hR hS hC (suppP k)
        (juxtP_of_fineUniq hA hM hR hS hC (GlobalTheory.T.segment_product_word_in_shuffle hA (GlobalTheory.T.segment_jacquet_all hA hZ)) (GlobalTheory.T.irreducible_sub_segment_product hA hZ))
        linkP minP (peelGood HS hSoc)
      free := hF
      soc := hSoc
      jac := GlobalTheory.T.segment_jacquet_all hA hZ
      seg := fun Δ => GlobalTheory.T.exists_segment_representation hA Δ
      unl := hI
      com := hCm }

end CompanionTheory.Groth

end
end

section
namespace CompanionTheory.Groth

theorem groth_of_three (hZ : GlobalTheory.Published.SegmentRepresentation)
    (hI : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.Cos.LUnlinkedIrr k)
    (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      CompanionTheory.Exh.MidP k ∧ CompanionTheory.Exh.RefineP k ∧ CompanionTheory.Exh.SwapP k) : GlobalTheory.Published.GrothendieckRingPolynomial :=
  groth_of_cls fun k _ _ _ _ => cls_of hZ k (hI k) (H k)

end CompanionTheory.Groth
end

section
namespace CompanionTheory.Groth

theorem grothendieckRingPolynomial_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.GrothendieckRingPolynomial :=
  groth_of_three hZ (fun k _ _ _ _ => CompanionTheory.Exh.lUnlinkedIrr_of_seg hZ k) fun k _ _ _ _ =>
    ⟨CompanionTheory.Exh.midP' k CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top, CompanionTheory.Exh.refineP' k,
      CompanionTheory.Exh.swapP' k (ClsOfF.comm_of (CompanionTheory.Exh.lUnlinkedIrr_of_seg hZ k))⟩

end CompanionTheory.Groth
end
