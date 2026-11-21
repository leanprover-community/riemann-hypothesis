import Mathlib
import Formalism.LocalToGlobal.Divisibility.DivisibilityConstruction.ShiftOfColTie
import Formalism.LocalToGlobal.Divisibility.ColPins
import Development.AbelianVarietyTheory.Definitions.Divisors.KerSizes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesTildeGammaValuesStatement
import Formalism.LocalToGlobal.Divisibility.NumbersLink
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerChainMatricesWithNormBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvFrameOfPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamFramedOfPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatFramedOfGramPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColsInIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHtNumsOfKerSideLastSide
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastMapNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodBoundLastLog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsInterlaceSameShift
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeWordLocalConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthNormLogBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastSideLogBound
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormsMatrixStepsCoupledFactorBoundedAnyLevelPrim
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PaddedWittNormSquare
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PaddedLastEntry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFockLSqLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyNonzeroThetaVectorsNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
import Formalism.LocalToGlobal.GlobalTheory.GL3.ConjugateTorsionPointExists
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaZeroMeanLogNormConjugatesOfWeber
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticePeriodEtaObj
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaWeberStatement
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
import BuildAid.ForwardExisting
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Period
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanLogPeriodConjugatesEqChowlaSelberg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeOfEqSpanFracSmul

section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_word_local_constants : ColumnNorms → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod → GlobalTheory.ColNorms.FamilyVectors → GlobalTheory.ColNorms.FamilyNorms → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (N : NumDatum) (X : Fields) [IsTotallyComplex X.K] (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (B : Base D D.host.ccK dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) (b : I.β (N.R.m - 2 + 1)) (hY : YbHyp (R := N.R) sel mu cst I u (N.R.m - 2) b) (hK : KerEquivC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch)) (hF : ∀ j, (chF W sel mu I u j).Ok) (hE : (evGSD W Ch sel mu (rPsymF Ch) u).Ok) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)), HostTie N s Pr → WeightTie N W pl u δ → CharTie N s W Ch G sel → AnalyticTie D dl χ cD → mu = 1 → cst.sharp = true → I.Ok Ch sel mu cst G (N.R.m - 2) → FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → Sizes Pr W N.sc.a → SizeRows N δ (Pr.T u) → Reads N eJ δ (Pr.T u) R → KerSide R (InfinitePlace X.K) C (FactorBounds (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) fun l => (eJ l).1) := by
  first | exact @GlobalTheory.KernelHalf.kerSide_chain | exact GlobalTheory.KernelHalf.kerSide_chain | (intros; apply GlobalTheory.KernelHalf.kerSide_chain <;> assumption)
end

section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_side_log_bound : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.OrthNormLogBound → ∀ (N : NumDatum) (X : Fields) (Pr : Primes X) (W : Wts X Pr.Word N.R) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)), WeightTie N W pl u δ → Sizes Pr W N.sc.a → SizeRows N δ (Pr.T u) → 1 ≤ Pr.T u → Reads N eJ δ (Pr.T u) R → LastSide R 25 (lastLog W u) := by
  first | exact @GlobalTheory.ColRows.LastSideProof.lastSide | exact GlobalTheory.ColRows.LastSideProof.lastSide | (intros; apply GlobalTheory.ColRows.LastSideProof.lastSide <;> assumption)
end

section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRowsTop

open GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum GlobalTheory.ColNorms GlobalTheory.PeriodClassSum GlobalTheory.LastPeriod in

theorem periodFun_le (hL : LastMapNorm) {X : Fields} (hX : X.Ok) {Pr : Primes X} (hPr : Pr.Ok) {R : Ranks} (W : Wts X Pr.Word R)
    (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ)
    (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) (hI : ∀ τ, Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ))
    (hS : ∀ τ, Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ)) (s : X.K →+* ℂ)
    (ψ : RowPt Pr R sel (mu0 X.F X.E X.K Sg) → Formalism.L2.DIV.VV X.K (W.lamTrue u R.m))
    (F : RowPt Pr R sel (mu0 X.F X.E X.K Sg) → Formalism.L2.DIV.VV X.K W.sgTrue) :
    ‖s (PtilFF W Ch sel (mu0 X.F X.E X.K Sg) P (mtildeOk W Ch sel (mu0 X.F X.E X.K Sg) hX P) u ψ F)‖ ^ 2 ≤
      Real.exp (lastLog W u) *
        GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (evGSD W Ch sel (mu0 X.F X.E X.K Sg) P u) (GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.evOk W Ch sel Sg hX hPr P u) s ψ *
        GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P) (mtildeOk W Ch sel (mu0 X.F X.E X.K Sg) hX P) s F := by
  have hT : (0 : ℝ) < (Pr.T u : ℝ) := Nat.cast_pos.2 (hPr.T_prime u).pos
  have ht : ∀ τ, star (s (X.emb τ (star ((Pr.piT u : 𝓞 X.E) : X.E)))) * s (X.emb τ (star ((Pr.piT u : 𝓞 X.E) : X.E))) =
      ((Pr.T u : ℝ) : ℂ) := fun τ => by
    have h1 := hX.conjE (s.comp (X.emb τ)) (star ((Pr.piT u : 𝓞 X.E) : X.E))
    rw [star_star, RingHom.comp_apply, RingHom.comp_apply, starRingEnd_apply] at h1
    have h2 : ((Pr.piT u : 𝓞 X.E) : X.E) * star ((Pr.piT u : 𝓞 X.E) : X.E) = (Pr.T u : X.E) := by
      have := congrArg (fun z : 𝓞 X.E => (z : X.E)) (hPr.piT_norm u)
      simp only [map_mul, map_natCast] at this
      exact this
    rw [← h1, ← map_mul, ← map_mul, h2]
    simp
  have hB := coefOpLe_brAt hL s (N_m_succ R) (W.lamTrue u R.m) W.sgTrue hI hS _ hT _ ht
  set hM := mtildeOk W Ch sel (mu0 X.F X.E X.K Sg) hX P
  set hE := GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.evOk W Ch sel Sg hX hPr P u
  let _ := hM.fintypeCl
  have h := sum_pair_le s _ _ _ _ hB ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt
    (fun c => ψ ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c))
    (fun c => F ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c))
  have e0 : PtilFF W Ch sel (mu0 X.F X.E X.K Sg) P hM u ψ F =
      ∑ c, ((((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt c : ℕ) : X.K)⁻¹ *
        pairBK W.sgTrue (brC W u (ψ ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)))
          (F ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)) := by
    unfold PtilFF GSD.csOf
    exact (LinearMap.congr_fun (LinearMap.sum_apply _ _ _) _).trans (LinearMap.sum_apply _ _ _)
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (evGSD W Ch sel (mu0 X.F X.E X.K Sg) P u) hE s ψ =
      ∑ c, ((((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt c : ℕ) : ℝ)⁻¹ *
        sqAt s (W.lamTrue u R.m) (ψ ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt GSD.ipAt
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact (re_inv_mul _ _).trans
      (congrArg₂ (· * ·) rfl ((gram_posSemidef_and_sqAt X.E X.K X.Tau X.emb _ (W.lamTrue u R.m) s).2 _))
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P) hM s F =
      ∑ c, ((((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt c : ℕ) : ℝ)⁻¹ *
        sqAt s W.sgTrue (F ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt GSD.ipAt
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hg := (gram_posSemidef_and_sqAt X.E X.K X.Tau X.emb _ W.sgTrue s).2
    simp only [pairVr_one_eq, pairK_one_basis] at hg
    refine (re_inv_mul _ _).trans (congrArg₂ (· * ·) rfl (Eq.trans ?_ (hg _)))
    unfold GSD.pairAt
    rw [row_gramV]
    rfl
  rw [e0, e1, e2]
  refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ ?_) ?_)
  · rw [lastLog, Real.exp_add, mul_comm (-_ : ℝ), ← Real.rpow_def_of_pos hT, ← Int.cast_neg, Real.rpow_intCast]
    exact mul_le_mul_of_nonneg_left (Real.le_exp_log _) (by positivity)
  · exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (sqAt_nonneg _ _ _)
  · exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (sqAt_nonneg _ _ _)

theorem period_le (hL : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.LastMapNorm) {X : Fields} (hX : X.Ok) {Pr : Primes X} (hPr : Pr.Ok) {R : Ranks}
    (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (mu : Tup X.F X.E X.K Sg) (hmu : mu = 1)
    (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) (hI : ∀ τ, Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ))
    (hS : ∀ τ, Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ))
    (hP : (mtildeGSD W Ch sel mu P).Ok) (hE : (evGSD W Ch sel mu P u).Ok) (v : InfinitePlace X.K)
    (ψ : RowPt Pr R sel mu → Formalism.L2.DIV.VV X.K (W.lamTrue u R.m)) (F : RowPt Pr R sel mu → Formalism.L2.DIV.VV X.K W.sgTrue) :
    v (PtilFF W Ch sel mu P hP u ψ F) ^ 2 ≤
      Real.exp (lastLog W u) * ((evGSD W Ch sel mu P u).ipAt hE v ψ ψ).re * ((mtildeGSD W Ch sel mu P).ipAt hP v F F).re := by
  subst hmu
  have h := periodFun_le hL hX hPr W Ch sel Sg P u hI hS v.embedding ψ F
  rw [InfinitePlace.norm_embedding_eq] at h
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt, InfinitePlace.mk_embedding] at h
  exact h

theorem ipAt_nonneg_of_datFramed {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} {h : S.Ok} (hS : DatFramed S h)
    (v : InfinitePlace K) (ψ : S.EqFun) : 0 ≤ (S.ipAt h v ψ ψ).re := by
  obtain ⟨n, e, X, -, hX⟩ := hS
  obtain ⟨y, rfl⟩ := e.surjective ψ
  rw [← hX v y, Complex.ofReal_re]
  positivity

theorem rowsBody_colFace : ColumnNorms → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod → GlobalTheory.ColNorms.FamilyVectors → GlobalTheory.ColNorms.FamilyNorms → ∃ C0 : ℝ, ∀ (D : D7) (N : NumDatum) (X : Fields) [IsTotallyComplex X.K] (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (hX : X.Ok) (Bs : DefBase X.K) (Df : DefSide Bs) (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs N.R.r → X.K)) (mu : Bs.Tup → Tup X.F X.E X.K Sg) (cst : ∀ t, LocCst X (rowSG Pr sel (mu t))) (I : ∀ t, ChIdx X Pr N.R (QE sel (mu t : Chr X.F X.E X.K))) (hL : ∀ t, (I t).Ok Ch sel (mu t) (cst t) G (N.R.m - 2)) (hP : ∀ t, (mtildeGSD W Ch sel (mu t) (rPsymF Ch)).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (I t).β (N.R.m - 2 + 1)) (hY : ∀ t x, YbHyp (R := N.R) sel (mu t) (cst t) (I t) (wd x) (N.R.m - 2) (b t x)) (dl : ℂ) (B : Base D D.host.ccK dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (hK : ∀ t x, KerEquivC W Ch sel (mu t) (cst t) (I t) (ambOf s B χ cD) (wd x) (N.R.m - 2) (b t x) (hY t x) (rPsymF Ch)) (hF : ∀ t x j, (chF W sel (mu t) (I t) (wd x) j).Ok) (hE : ∀ x, (evGSD W Ch sel (mu Bs.μ0) (rPsymF Ch) (wd x)).Ok) (ev : ∀ t, (Fin (Df.nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg (rPsymF Ch)) (pl : RPl N.R ≃ X.Tau) (x : Mem) (δ : Code N) (eJ : Bs.J ≃ Fin N.R.m) (R : RecNums Bs.J (RPl N.R)), HostTie N s Pr → WeightTie N W pl (wd x) δ → CharTie N s W Ch G sel → AnalyticTie D dl χ cD → mu Bs.μ0 = 1 → (cst Bs.μ0).sharp = true → FieldOfDefinition W sel (mu Bs.μ0) (cst Bs.μ0) (wd x) (ambOf s B χ cD) → Sizes Pr W N.sc.a → SizeRows N δ (Pr.T (wd x)) → Reads N eJ δ (Pr.T (wd x)) R → C0 ≤ R.Ch → (∀ v : InfinitePlace X.K, ((Df.HV Bs.μ0).map v.embedding).PosDef) → (∀ X0, IsFrames Df X0 → ∀ v F, ((mtildeGSD W Ch sel (mu Bs.μ0) (rPsymF Ch)).ipAt (hP Bs.μ0) v ((ev Bs.μ0 F).1).1 ((ev Bs.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K (Fin (Df.nV Bs.μ0))) X0 v F ^ 2) → RowsBody (colFace hX Df Xg mu cst I hL hP Mem wd b hY (kerRec mu cst I wd b hY (ambOf s B χ cD) hK) hF ev) x (memQ (A := kerRec mu cst I wd b hY (ambOf s B χ cD) hK) (hF := hF) hE (x := x)) (colsIn W Ch hX sel (mu Bs.μ0) (cst Bs.μ0) (I Bs.μ0) (hL Bs.μ0) (wd x)) R ∧ ∀ v, IsUnit ((MramH W Ch hX (wd x)).X v).det := by
  intro h1 h2 h3 h4
  obtain ⟨C, hC, hker⟩ := GlobalTheory.T.prime_word_local_constants h1 h2 h3 h4
  refine ⟨max (2 * (16 + 25)) (max (6 * C + 1 + 2 * C * C) (4 * C * (25 + C))), ?_⟩
  intro D N X _ s Pr W Ch G sel Sg hX Bs Df Xg mu cst I hL hP Mem wd b hY dl B χ cD hK hF hE ev pl x δ eJ R
    hHost hWt hChar hAn hmu hsharp hFD hS hR hRd hC0 hpos hev
  have hPr : Pr.Ok := hHost.2.2.2.2.2.2.2.2.2.1
  have hT : 1 ≤ Pr.T (wd x) := (hPr.T_prime _).one_le
  have hk := hker D N X s Pr W Ch G sel Sg (mu Bs.μ0) (cst Bs.μ0) (I Bs.μ0) dl B χ cD pl (wd x) δ (b Bs.μ0 x) (hY Bs.μ0 x)
    (hK Bs.μ0 x) (hF Bs.μ0 x) (hE x) Bs.J eJ R hHost hWt hChar hAn hmu hsharp (hL Bs.μ0) hFD hS hR hRd
  have hl := GlobalTheory.T.last_side_log_bound GlobalTheory.BranchLogBound.orthNormLogBound N X Pr W pl (wd x) δ Bs.J eJ R hWt hS hR hT hRd
  obtain ⟨hn, hA, hsz⟩ := GlobalTheory.ColRows.exists_htNums_of_kerSide_lastSide Bs.J (RPl N.R) (InfinitePlace X.K) R C 25 _ _ hC (by norm_num)
    ((le_max_left _ _).trans hC0) (((le_max_left _ _).trans (le_max_right _ _)).trans hC0)
    (((le_max_right _ _).trans (le_max_right _ _)).trans hC0) hk hl
  obtain ⟨X0, hX0⟩ := GlobalTheory.ColRows.exists_isFrames X.K Bs Df hpos
  obtain ⟨hdet, hiso⟩ := GlobalTheory.ColFirstIso.colsIn_isometry X hX Pr N.R W Ch sel Sg (mu Bs.μ0) (cst Bs.μ0) (I Bs.μ0) G _ (hL Bs.μ0)
    (wd x) (hF Bs.μ0 x 0) hmu
  obtain ⟨hint, hsh⟩ := GlobalTheory.ColRows.weights_interlace_sameShift N X Pr W pl (wd x) δ hWt hR
  have hdat := GlobalTheory.ColRows.evGSD_datFramed X hX Pr N.R W Ch sel Sg (mu Bs.μ0) (rPsymF Ch) (wd x) (hE x)
  refine ⟨GlobalTheory.T.kerChain_matrices_with_norm_bounds X.K Bs Df (colFace hX Df Xg mu cst I hL hP Mem wd b hY (kerRec mu cst I wd b hY (ambOf s B χ cD) hK) hF ev) x
    (memQ (A := kerRec mu cst I wd b hY (ambOf s B χ cD) hK) (hF := hF) hE (x := x)) _
    (colPerL (hP Bs.μ0) Xg (wd x) (ev Bs.μ0)) (RPl N.R) R hn (fun l => (eJ l).1) X0 hdet hiso
    (fun i => GlobalTheory.FamilyFrames.famFramed_chF X hX Pr N.R W Ch sel Sg (mu Bs.μ0) (I Bs.μ0) (wd x) i (hF Bs.μ0 x i)) hdat
    (fun φ F => colPer_eq hX (hP Bs.μ0) Xg _ (hF Bs.μ0 x) (hE x) (hL Bs.μ0) (ev Bs.μ0) φ F) hX0 hsz ?_, hdet⟩
  intro v ψ F
  have hb := period_le GlobalTheory.BranchNorm.lastMapNorm hX hPr W Ch sel (mu Bs.μ0) hmu (rPsymF Ch) (wd x) hint hsh (hP Bs.μ0) (hE x) v
    ψ.1 (ev Bs.μ0 F).1.1
  rw [hA]
  exact hb.trans (mul_le_mul_of_nonneg_left (hev X0 hX0 v F)
    (mul_nonneg (Real.exp_pos _).le (ipAt_nonneg_of_datFramed hdat v ψ)))

end GlobalTheory.ColRowsTop
end

section
noncomputable section

namespace GlobalTheory.Proof.WeightSequenceEntries

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke

theorem padZero_eq {a : ℕ} (b : ℕ) (ν : DomWeight a) (j : Fin b) :
    PaddedWittNormSquare.padZero b ν j = PaddedLastEntry.padZero b ν j := rfl

theorem lastEntry_eq {a : ℕ} (ν : DomWeight a) : PaddedWittNormSquare.lastEntry ν = PaddedLastEntry.lastEntry ν := rfl

theorem normSq_eq {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (v : VV ℂ lam) :
    PaddedWittNormSquare.normSq lam v = PaddedLastEntry.invNormSq lam v := rfl

theorem unitSq_eq {ι : Type} [Fintype ι] {a b : ℕ} (r : ι → ℝ) (z : VCx ι a b) :
    PaddedWittNormSquare.unitNormSq r z = PaddedLastEntry.unitSq r z := rfl

theorem tmax_eq {ι : Type} [Fintype ι] {a : ℕ} (b : ℕ) (ν : ι → DomWeight a) (Om : ι → ℝ) (S : ℝ) :
    PaddedWittNormSquare.tmax b ν Om S = PaddedLastEntry.tmax b ν S Om := rfl

theorem opNormSqLe_iff {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (t : ℝ) :
    PaddedWittNormSquare.OpNormSqLe lam lam' T t ↔ PaddedLastEntry.OpNormSqLe lam lam' T t := by
  unfold PaddedWittNormSquare.OpNormSqLe PaddedLastEntry.OpNormSqLe
  simp only [normSq_eq]

theorem stepWeights_iff {a b : ℕ} (lam ν : DomWeight a) (lam' : DomWeight b) :
    (∃ s' s : ℤ, PaddedWittNormSquare.IsStepWeight lam ν lam' s' s) ↔ PaddedLastEntry.StepWeights lam ν lam' := by
  unfold PaddedWittNormSquare.IsStepWeight PaddedLastEntry.StepWeights
  constructor
  · rintro ⟨s', s, hν, hpos, hpad⟩
    exact ⟨hpos, ⟨s', hν⟩, ⟨s, fun j => (hpad j).trans (padZero_eq b ν j)⟩⟩
  · rintro ⟨hpos, ⟨s', hν⟩, ⟨s, hpad⟩⟩
    exact ⟨s', s, hν, hpos, fun j => (hpad j).trans (padZero_eq b ν j).symm⟩

theorem stepWeights_family_iff {ι : Type} {a b : ℕ} (lam ν : ι → DomWeight a) (lam' : ι → DomWeight b) :
    (∃ s' s : ι → ℤ, ∀ τ, PaddedWittNormSquare.IsStepWeight (lam τ) (ν τ) (lam' τ) (s' τ) (s τ)) ↔
      ∀ τ, PaddedLastEntry.StepWeights (lam τ) (ν τ) (lam' τ) := by
  constructor
  · rintro ⟨s', s, h⟩ τ
    exact (stepWeights_iff (lam τ) (ν τ) (lam' τ)).1 ⟨s' τ, s τ, h τ⟩
  · intro h
    choose s' s hs using fun τ => (stepWeights_iff (lam τ) (ν τ) (lam' τ)).2 (h τ)
    exact ⟨s', s, hs⟩

theorem guard_iff {ι : Type} {a b : ℕ} (hab : a ≤ b) (ν : ι → DomWeight a) :
    (∀ τ, a < b ∨ PaddedWittNormSquare.lastEntry (ν τ) = 0) ↔ (a = b → ∀ τ, PaddedLastEntry.lastEntry (ν τ) = 0) := by
  constructor
  · intro h heq τ
    rcases h τ with hlt | h0
    · exact absurd heq (ne_of_lt hlt)
    · exact (lastEntry_eq (ν τ)).symm.trans h0
  · intro h τ
    rcases lt_or_eq_of_le hab with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ((lastEntry_eq (ν τ)).trans (h heq τ))

theorem growth_iff {ι : Type} [Fintype ι] {a b : ℕ} (G : VCx ι a b → ℂ) (S : ℝ) (r : ι → ℝ) :
    (∀ z, ‖G z‖ ≤ S * Real.exp (PaddedWittNormSquare.unitNormSq r z / 2)) ↔
      ∀ z, ‖G z‖ ≤ S * Real.exp (PaddedLastEntry.unitSq r z / 2) := by
  simp only [unitSq_eq]

theorem conclusion_iff {ι : Type} [Fintype ι] {a b : ℕ} (lam ν : ι → DomWeight a) (lam' : ι → DomWeight b)
    (G : VCx ι a b → ℂ) (S : ℝ) (Om : ι → ℝ) (cD : ι → ℂ) :
    PaddedWittNormSquare.OpNormSqLe lam lam' (jetOp lam lam' (jetC cD G) fun τ => PaddedWittNormSquare.lastEntry (ν τ)) (PaddedWittNormSquare.tmax b ν Om S) ↔
      PaddedLastEntry.OpNormSqLe lam lam' (jetOp lam lam' (jetC cD G) fun τ => PaddedLastEntry.lastEntry (ν τ)) (PaddedLastEntry.tmax b ν S Om) := by
  simp only [opNormSqLe_iff, tmax_eq, lastEntry_eq]

theorem blockBound_iff : PaddedWittNormSquare.BlockBound ↔ PaddedLastEntry.BlockBound := by
  unfold PaddedWittNormSquare.BlockBound PaddedLastEntry.BlockBound
  constructor
  · intro h ι _ a b hab lam ν lam' hstep hguard r Om cD hr hOm hc G S hG hgrowth
    obtain ⟨s', s, hs⟩ := (stepWeights_family_iff lam ν lam').2 hstep
    exact (conclusion_iff lam ν lam' G S Om cD).1
      (h ι a b hab lam ν lam' s' s hs ((guard_iff hab ν).2 hguard) G S r Om cD hG hr
        ((growth_iff G S r).2 hgrowth) hOm hc)
  · intro h ι _ a b hab lam ν lam' s' s hs hguard G S r Om cD hG hr hgrowth hOm hc
    exact (conclusion_iff lam ν lam' G S Om cD).2
      (h ι a b hab lam ν lam' ((stepWeights_family_iff lam ν lam').1 ⟨s', s, hs⟩)
        ((guard_iff hab ν).1 hguard) r Om cD hr hOm hc G S hG ((growth_iff G S r).1 hgrowth))

end GlobalTheory.Proof.WeightSequenceEntries
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFamily_nonzeroThetaVectors_numberField : GlobalTheory.ColNorms.FamilyVectors := by
  first | exact @GlobalTheory.ColNorms.familyVectors | exact GlobalTheory.ColNorms.familyVectors | (intros; apply GlobalTheory.ColNorms.familyVectors <;> assumption)
end

section
section
open Formalism.BasicNotions

namespace GlobalTheory.Theta0MeanLeC

theorem theta0MeanLeC : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D :=
  (GlobalTheory.T.thetaZero_mean_log_norm_conjugates_of_weber GlobalTheory.LatticePeriodEtaObj.latticePeriodEta_obj GlobalTheory.ThetaWeberObj.thetaWeberStatement).1.2.2

end GlobalTheory.Theta0MeanLeC
end

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaZeroMeanLogLeConstMul : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D := by
  atlas_forward_decl GlobalTheory.Theta0MeanLeC.theta0MeanLeC
end

section
section
noncomputable section
namespace GlobalTheory.ColNorms.FamilyBound
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity GlobalTheory.ColNorms

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem genusOne_meanSquare_forms_agree (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : StandardLatticesGL3.nrm1Sq Λ G = GL3Theta.normSq1 Λ G :=
  (GlobalTheory.Glob.normSq1_eq_nrm1Sq Λ G).symm

theorem conj_normSq (B : Base D cc δ) (χ : IdE D → ℂ) (hc : StandardLatticesGL3.Crv D cc δ) (ht : StandardLatticesGL3.natTie D cc δ (B.eNat χ))
    {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : admitted D N N' L L') (M : IntermediateField ℚ ℂ) (hD : DataIn D (tor0 D cc δ) M)
    (hcoef : CoefIn D (B.eNat χ N N' L L') M) (ρ : M →ₐ[ℚ] ℂ) {t : ℂ}
    (hT : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t) :
    normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L') (fnConj D M ρ (B.eNat χ N N' L L')) =
      GL3Theta.normSq1 (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t) ^ (fF D * N * N') := by
  rw [(GlobalTheory.ConjNorm.useNorm_all D cc δ hc _ B.t0 N N' L L' (StandardLatticesGL3.admissible_self_dual_even hA).1 (StandardLatticesGL3.admissible_self_dual_even hA).2.1 (StandardLatticesGL3.admissible_self_dual_even hA).2.2 _
    (ht _ B.t0 N N' L L' hA) M ρ hD hcoef t hT).1, genusOne_meanSquare_forms_agree]

theorem conj_indep (B : Base D cc δ) (χ : IdE D → ℂ) (hc : StandardLatticesGL3.Crv D cc δ) (ht : StandardLatticesGL3.natTie D cc δ (B.eNat χ)) :
    ThetaNormConjugateIndependent D (tor0 D cc δ) (B.eNat χ) := by
  intro N N' L₁ L₁' L₂ L₂' a₁ a₂ M _ hD c₁ c₂ ρ
  have : NumberField M := NumberField.mk
  obtain ⟨t, hT⟩ := GlobalTheory.Glob.exists_isThetaZero hc hD ρ
  rw [conj_normSq B χ hc ht a₁ M hD c₁ ρ hT, conj_normSq B χ hc ht a₂ M hD c₂ ρ hT]

theorem mean_le_of {C : ℝ} (hC : GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D) (B : Base D cc δ) (χ : IdE D → ℂ) (hc : StandardLatticesGL3.Crv D cc δ)
    (ht : StandardLatticesGL3.natTie D cc δ (B.eNat χ)) : ThetaMeanBound D (tor0 D cc δ) C (B.eNat χ) := by
  intro Lsc hL N N' L L' hA M _ hD hcoef
  have : NumberField M := NumberField.mk
  have hex : ∀ ρ : M →ₐ[ℚ] ℂ, ∃ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t := fun ρ => GlobalTheory.Glob.exists_isThetaZero hc hD ρ
  choose t hT using hex
  have hm := hC cc δ M t ⟨hc.1, hc.2, hD, hT⟩ Lsc hL
  have key : meanLogNormSq D (tor0 D cc δ) L L' M (B.eNat χ N N' L L') =
      ((fF D * N * N' : ℕ) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.meanLog M (lamOf D cc δ) t := by
    unfold meanLogNormSq GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.meanLog GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.conjNormSq
    simp_rw [fun ρ => conj_normSq B χ hc ht hA M hD hcoef ρ (hT ρ), Real.log_pow]
    rw [← Finset.mul_sum, mul_div_assoc]
    rfl
  rw [key]
  calc ((fF D * N * N' : ℕ) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.meanLog M (lamOf D cc δ) t
      ≤ ((fF D * N * N' : ℕ) : ℝ) * (C * Lsc) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = C * (fF D : ℝ) * (N : ℝ) * (N' : ℝ) * Lsc := by push_cast; ring

theorem familyNorms_of (hT : FamilyTie) (hM : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D) : FamilyNorms := by
  obtain ⟨C, -, hC⟩ := hM
  refine ⟨C, fun D cc δ B χ h1 h2 hcc hδ hχ hY => ?_⟩
  have ht := hT D cc δ B χ h1 h2 hcc hδ hχ hY
  have hc : StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have h14 := theta_link_holds D cc hcc δ hδ B (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ) χ hχ
  exact ⟨h14.1, mean_le_of (hC D) B χ hc ht, conj_indep B χ hc ht, h14.2⟩

theorem familyNorms : FamilyNorms := familyNorms_of GlobalTheory.T.normalisedFamily_eq_tensorPower_vacuum GlobalTheory.T.exists_thetaZeroMeanLogLeConstMul

end GlobalTheory.ColNorms.FamilyBound
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFamily_normBound_absoluteConstant : GlobalTheory.ColNorms.FamilyNorms := by
  atlas_forward_decl GlobalTheory.ColNorms.FamilyBound.familyNorms
end

section
section
noncomputable section

namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

theorem periodLattices : PeriodLattices := by
  intro D X s cc δ B χ cD _hX hok _h1 _h2 hcc hδ _hχ _hdg _hY a b S ha hb hconj hU
  exact ⟨KS.Lat.delta_ne hcc hδ, nonempty_tau s, hconj, hU, aa_fg s cc,
    fun N N' hN hN' => ⟨e_fixed_ambOf s B χ cD N N' hok hcc hδ (s.admissible_of_selfDual_lattices hok ha hb hN hN'),
      laFacts_ambOf s B χ cD N N' hok hcc hδ (s.admissible_of_selfDual_lattices hok ha hb hN hN')⟩⟩

end GlobalTheory.ColNorms
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFamily_periodLattice_properties_hold : GlobalTheory.ColNorms.PeriodLattices := by
  atlas_forward_decl GlobalTheory.ColNorms.periodLattices
end

section
section
namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain Formalism.L2.Ker

theorem coset_refinement : CosetRefinement := by
  intro X A a b S Md _ _ hOdd hLa
  exact indAdd_of A a b S Md hOdd.pos (lattice_classes_finite_refinement X a b S) (indTieD_of_la A a b S Md hOdd.pos hLa)

end GlobalTheory.ColNorms
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetIndicatorThetaRefinement_proof : GlobalTheory.ColNorms.CosetRefinement := by
  atlas_forward_decl GlobalTheory.ColNorms.coset_refinement
end

section
section
noncomputable section

namespace GlobalTheory.MeanPeriodClosed

open NumberField Formalism.BasicNotions
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5 (brN br_meanLogOm_eq br_b_spec absNorm_inv_mul_different natAbs_discr_eq
  discr_K discriminant_mod_four br_sqrt_sq br_finrank_K br_finrank_E)

theorem two_log_brN (D : D7) :
    (2 / (Module.finrank ℚ D.host.E : ℝ)) * Real.log (brN D) =
      Real.log D.host.rdE - Real.log (Real.sqrt (D.host.d : ℝ)) := by
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  have hd0 : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hdK : NumberField.discr D.host.K = -(D.host.d : ℤ) :=
    discr_K D.host.K D.host.d (discriminant_mod_four D) _ (br_sqrt_sq D) (br_finrank_K D)
  have h1 := absNorm_inv_mul_different D.host.K D.host.E D.host.conj D.host.𝔟 (br_b_spec D)
  have h2 := natAbs_discr_eq D.host.K D.host.E D.host.d hdK
  set A : ℝ := (Ideal.absNorm (differentIdeal (𝓞 D.host.K) (𝓞 D.host.E)) : ℝ) with hA
  have hsq : brN D ^ 2 = A := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h1
    simp only [Rat.cast_pow, Rat.cast_natCast] at this
    rw [hA, ← this]
    rfl
  set m : ℕ := Module.finrank D.host.K D.host.E with hm
  have hE : Module.finrank ℚ D.host.E = 2 * m := br_finrank_E D
  have hm0 : (m : ℝ) ≠ 0 := by
    have : 0 < m := Module.finrank_pos
    exact_mod_cast this.ne'
  have hdisc : |(NumberField.discr D.host.E : ℝ)| = A * (D.host.d : ℝ) ^ m := by
    have := congrArg (fun n : ℕ => (n : ℝ)) h2
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs] at this
    rw [hA, ← this]
  have hdisc0 : |(NumberField.discr D.host.E : ℝ)| ≠ 0 := by
    simpa using NumberField.discr_ne_zero D.host.E
  have hA0 : A ≠ 0 := fun h => hdisc0 (by rw [hdisc, h, zero_mul])
  have hlogA : 2 * Real.log (brN D) = Real.log A := by
    rw [← hsq, Real.log_pow]; push_cast; ring
  have hrd : Real.log D.host.rdE =
      (Real.log A + (m : ℝ) * Real.log D.host.d) / (2 * (m : ℝ)) := by
    unfold Formalism.BasicNotions.Host.rdE
    rw [Real.log_rpow (abs_pos.2 (by simpa using NumberField.discr_ne_zero D.host.E)), hdisc,
      Real.log_mul hA0 (pow_ne_zero _ hd0.ne'), Real.log_pow, hE]
    push_cast
    field_simp
  rw [hrd, Real.log_sqrt hd0.le, hE]
  push_cast
  field_simp
  linear_combination hlogA

theorem meanPeriodAt (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriodAt D cc δ := by
  intro M _ hM τ
  have hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hpos : ∀ ρ : M →ₐ[ℚ] ℂ,
      0 < Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.area (Formalism.MainNotions.TaylorLogMetric.lamConj M ρ (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) :=
    fun ρ => GlobalTheory.Glob.area_lamConj_pos hc hM ρ
  have hmean := GlobalTheory.PeriodMean.mean_log_period D (GlobalTheory.InducedType.induced_type D).1 cc δ hc M
    hM.2.1 hM.2.2
  have e := br_meanLogOm_eq D (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) M hM.1 τ hpos
  have hN := two_log_brN D
  show Formalism.MainNotions.TaylorLogMetric.meanLogOm D (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) M τ = Formalism.MainNotions.TaylorLogMetric.logOmVal D
  rw [e, GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.logOmVal_eq]
  have hmean' : (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.area
      (Formalism.MainNotions.TaylorLogMetric.lamConj M ρ (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / Real.pi)) / (Module.finrank ℚ M : ℝ) =
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi / Real.sqrt D.host.d) -
        Formalism.MainNotions.TaylorLogMetric.logDerivativeAtOne D := hmean
  rw [hmean']
  have hd0 : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have hr0 : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_pos_of_pos (abs_pos.2 (by simpa using NumberField.discr_ne_zero D.host.E)) _
  rw [Real.log_div (by positivity) hd0.ne', Real.log_div (by positivity) hr0.ne']
  rw [neg_mul, hN]
  ring

theorem meanPeriod : GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod :=
  fun D cc δ hcc hδ => meanPeriodAt D cc δ hcc hδ

end GlobalTheory.MeanPeriodClosed
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanLogPeriod_chowlaSelberg : GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod := by
  atlas_forward_decl GlobalTheory.MeanPeriodClosed.meanPeriod
end

section
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.KernelHalfS

open GlobalTheory.ColNorms GlobalTheory.ColNorms.NumMean GlobalTheory.KernelHalf

theorem log_eight_leS (CY : ℝ) (N : NumDatum) (δ : Code N) (hS : GlobalTheory.Core.Ht2.SizeRowsS CY N δ) {i : ℕ} (hi : i < N.R.m) :
    Real.log (8 + 32 * ((N.R.f : ℝ) * ((N.R.N i : ℝ) * N.R.N (i + 1))) * N.v) ≤ 8 * N.sc.L := by
  obtain ⟨⟨hrd, -, -, hx4, -⟩, hg, hlT, hfN, hnu, -⟩ := hS
  have hA := N_le N (j := i) (by omega)
  have hB := N_le N (j := i + 1) (by omega)
  have hL := one_le_L N.sc
  have hb := two_le_b N.sc
  have hx := N.sc.one_lt_alt
  have hrd1 := one_le_rd N
  have hf := one_le_f N.R
  have hNb : (N.Nm : ℝ) ≤ N.sc.b := le_trans (le_mul_of_one_le_left (by positivity) hf) hfN
  have hAB : (N.R.N i : ℝ) * N.R.N (i + 1) ≤ (N.Nm : ℝ) ^ 2 := by rw [sq]; gcongr
  have hgb : (N.R.f : ℝ) * ((N.R.N i : ℝ) * N.R.N (i + 1)) ≤ N.sc.b ^ 2 := by
    calc _ ≤ (N.R.f : ℝ) * (N.Nm : ℝ) ^ 2 := by gcongr
      _ = ((N.R.f : ℝ) * N.Nm) * N.Nm := by ring
      _ ≤ N.sc.b * N.sc.b := by gcongr
      _ = _ := by ring
  have hrdb : N.rd ≤ N.sc.b := (Real.log_le_iff_le_exp (by linarith)).1 hrd
  have hxb : 4 * N.sc.x ≤ N.sc.b := (Real.log_le_iff_le_exp (by linarith)).1 hx4
  have hv0 : 0 ≤ N.v := by unfold NumDatum.v; linarith
  have hvb : N.v ≤ N.sc.b / 2 := by unfold NumDatum.v; linarith
  have hb3 : 8 ≤ N.sc.b ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ _ := by gcongr
  have hb5 : 32 ≤ N.sc.b ^ 5 := by
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ _ := by gcongr
  have := log_le_mul N.sc (y := 8 + 32 * ((N.R.f : ℝ) * ((N.R.N i : ℝ) * N.R.N (i + 1))) * N.v) (by positivity) 8 (by
    calc _ ≤ 8 + 32 * N.sc.b ^ 2 * (N.sc.b / 2) := by gcongr
      _ = 8 + 16 * N.sc.b ^ 3 := by ring
      _ ≤ 32 * N.sc.b ^ 3 := by linarith
      _ ≤ N.sc.b ^ 5 * N.sc.b ^ 3 := by gcongr
      _ = _ := by ring)
  simpa using this

theorem log_nu_leS (CY : ℝ) (N : NumDatum) (δ : Code N) (hS : GlobalTheory.Core.Ht2.SizeRowsS CY N δ) {i : ℕ} (hi : i < N.R.m) (z : RPl N.R) :
    Real.log (2 * ((N.nuAbs δ (i + 1) z : ℚ) : ℝ) + 2) ≤ 5 * N.sc.L := by
  obtain ⟨⟨hrd, -, -, hx4, -⟩, hg, hlT, hfN, hnu, -⟩ := hS
  have hj : i + 1 ∈ N.lifts := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hA := N_le N (j := i) (by omega)
  have hb := two_le_b N.sc
  have hx := N.sc.one_lt_alt
  have hf := one_le_f N.R
  have hNb : (N.Nm : ℝ) ≤ N.sc.b := le_trans (le_mul_of_one_le_left (by positivity) hf) hfN
  have hxb : 4 * N.sc.x ≤ N.sc.b := (Real.log_le_iff_le_exp (by linarith)).1 hx4
  have hb2 : 4 ≤ N.sc.b ^ 2 := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ _ := by gcongr
  have hb3 : 8 ≤ N.sc.b ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ _ := by gcongr
  have h0 : (0 : ℝ) ≤ ((N.nuAbs δ (i + 1) z : ℚ) : ℝ) := by
    have : 0 ≤ N.nuAbs δ (i + 1) z := Finset.sum_nonneg fun k hk => (hnu (i + 1) hj z k (Finset.mem_range.1 hk)).1
    exact_mod_cast this
  have h1 : ((N.nuAbs δ (i + 1) z : ℚ) : ℝ) ≤ (N.R.N i : ℝ) * (3 * N.sc.a) := by
    unfold NumDatum.nuAbs
    push_cast
    have := Finset.sum_le_card_nsmul (Finset.range (N.R.N i)) (fun k => ((N.nu δ (i + 1) z k : ℚ) : ℝ)) (3 * N.sc.a)
      fun k hk => (hnu (i + 1) hj z k (Finset.mem_range.1 hk)).2
    simpa using this
  have h2 : ((N.nuAbs δ (i + 1) z : ℚ) : ℝ) ≤ N.sc.b ^ 3 := by
    calc _ ≤ (N.R.N i : ℝ) * (3 * N.sc.a) := h1
      _ = (N.R.N i : ℝ) * (3 * N.sc.x) * N.sc.b := by unfold Scale.a; ring
      _ ≤ N.sc.b * N.sc.b * N.sc.b := by
          gcongr
          · linarith
          · linarith
      _ = _ := by ring
  have := log_le_mul N.sc (y := 2 * ((N.nuAbs δ (i + 1) z : ℚ) : ℝ) + 2) (by positivity) 5 (by
    calc _ ≤ 4 * N.sc.b ^ 3 := by linarith
      _ ≤ N.sc.b ^ 2 * N.sc.b ^ 3 := by gcongr
      _ = _ := by ring)
  simpa using this

set_option maxHeartbeats 1000000 in

theorem kerSide_of_meansS {J Emb α : Type} [Fintype J] [Fintype Emb] [Fintype α] (N : NumDatum) (δ : Code N) (T : ℕ) (hT : 2 ≤ T)
    (CY : ℝ) (hS : GlobalTheory.Core.Ht2.SizeRowsS CY N δ) (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)) (hR : Reads N eJ δ T R)
    (CK E Ct d : ℝ) (hCK : 0 ≤ CK) (hE : 0 ≤ E) (hCt : 0 ≤ Ct)
    (wt : Emb → α → ℝ) (h1 : ∀ v, ∑ a, wt v a = 1) (hmean : ∀ a, (∑ v, wt v a) / (Fintype.card Emb : ℝ) = 1 / d)
    (lo : α → RPl N.R → ℝ) (lt : α → ℝ) (hlo : ∀ z, (∑ a, lo a z) / d = N.logOm)
    (hlt : (∑ a, lt a) / d ≤ Ct * N.R.f * (2 * N.sc.L))
    (h n : ℕ → ℕ) (hh : ∀ l ≤ N.R.m, (h l : ℝ) ≤ Real.exp (E * errUnit N T))
    (hn : ∀ l ≤ N.R.m, (n l : ℝ) ≤ Real.exp (E * errUnit N T))
    (P : (J → Emb → ℝ) → Prop)
    (hP : ∀ t : J → Emb → ℝ, (∀ l v, t l v = ∑ a, wt v a * kernelBound_sq N δ T CK ((eJ l).1 + 1) (lo a)
        ((N.R.N (eJ l).1 : ℝ) * (N.R.N ((eJ l).1 + 1) : ℝ) * lt a) (h (eJ l).1) (h ((eJ l).1 + 1)) (n (eJ l).1) (n ((eJ l).1 + 1))) → P t) :
    KerSide R Emb (CK + 2 * E + 2 * Ct + 20 + 2 * max CY 0) P := by
  have hmx : 0 ≤ max CY 0 := le_max_right _ _
  obtain ⟨nL, na, nb, nLa, nm, nf, nk, nNn, nS, nη, nb', nlo⟩ := hR.nums
  have hL := one_le_L N.sc
  have hf := one_le_f N.R
  have hN := one_le_Nm N
  have hLL := L_le_La N
  have hg0 : (1 : ℝ) ≤ N.g 0 := by exact_mod_cast (N.g_prime 0).one_lt.le
  have hg1 : (1 : ℝ) ≤ N.g 1 := by exact_mod_cast (N.g_prime 1).one_lt.le
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (by omega : 1 ≤ T)
  have hlg0 : 0 ≤ Real.log ((N.g 0 : ℝ) * N.g 1) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hg0 hg1)
  have hlT0 : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg hT1
  have hlog : Real.log ((N.g 0 : ℝ) * N.g 1 * T) = Real.log ((N.g 0 : ℝ) * N.g 1) + Real.log (T : ℝ) :=
    Real.log_mul (by positivity) (by positivity)
  have hU0 : 0 ≤ errUnit N T := by
    unfold errUnit
    rw [hlog]
    positivity
  set C : ℝ := CK + 2 * E + 2 * Ct + 20 + 2 * max CY 0 with hC
  have hC0 : 0 ≤ C := by positivity
  have hX0 : 0 ≤ E * errUnit N T := mul_nonneg hE hU0
  unfold KerSide
  refine ⟨fun l => (N.R.N (eJ l).1 : ℝ) * (N.R.N ((eJ l).1 + 1) : ℝ),
    fun l _ => CK * N.R.f * (N.R.m : ℝ) ^ 2 * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1 * T) +
      (1 / 2) * Real.log ((h (eJ l).1 : ℝ) * h ((eJ l).1 + 1)) + (1 / 2) * Real.log ((n (eJ l).1 : ℝ) * n ((eJ l).1 + 1)),
    fun z v => ∑ a, wt v a * lo a z, fun v => (∑ a, wt v a * lt a) / N.R.f, fun _ => 0, fun _ => 0, N.v,
    Real.log ((N.g 0 : ℝ) * N.g 1), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ
    rw [wt_mean wt _ d hmean (fun a => lo a τ), hlo, nlo]
  · intro l _
    have hl := (eJ l).2
    have a1 := log_mul_le hX0 (hh (eJ l).1 hl.le) (hh ((eJ l).1 + 1) hl)
    have a2 := log_mul_le hX0 (hn (eJ l).1 hl.le) (hn ((eJ l).1 + 1) hl)
    rw [nf, nm, nNn, hR.logT]
    have e : CK * N.R.f * (N.R.m : ℝ) ^ 2 * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1 * T) = CK * errUnit N T := by
      unfold errUnit; ring
    have e2 : C * N.R.f * (N.R.m : ℝ) ^ 2 * (N.Nm : ℝ) ^ 2 * (Real.log ((N.g 0 : ℝ) * N.g 1) + Real.log (T : ℝ)) = C * errUnit N T := by
      unfold errUnit; rw [hlog]; ring
    rw [e, e2]
    have h3 : (CK + 2 * E) * errUnit N T ≤ C * errUnit N T := by
      refine mul_le_mul_of_nonneg_right ?_ hU0
      rw [hC]
      linarith
    have h4 : 0 ≤ C * N.R.f * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1) := by positivity
    linarith
  · have e : (∑ v, (∑ a, wt v a * lt a) / (N.R.f : ℝ)) / (Fintype.card Emb : ℝ) = ((∑ a, lt a) / d) / N.R.f := by
      rw [← Finset.sum_div, div_right_comm, wt_mean wt _ d hmean lt]
    rw [e, nL]
    have hf0 : (0 : ℝ) < N.R.f := by linarith
    rw [div_le_iff₀ hf0]
    refine hlt.trans ?_
    have : 2 * Ct ≤ C := by rw [hC]; linarith
    have h5 : 2 * Ct * N.sc.L ≤ C * N.sc.L := mul_le_mul_of_nonneg_right this (by linarith)
    have h7 := mul_le_mul_of_nonneg_right h5 hf0.le
    calc _ = 2 * Ct * N.sc.L * (N.R.f : ℝ) := by ring
      _ ≤ _ := h7
  · intro _
    rw [nf, nNn, nL, hR.logT]
    have : 0 ≤ N.sc.L := by linarith
    positivity
  · intro _
    rw [nf, nNn, nL, hR.logT]
    have : 0 ≤ N.sc.L := by linarith
    positivity
  · intro l
    have hl := (eJ l).2
    rw [nNn, sq]
    refine ⟨by positivity, ?_⟩
    exact mul_le_mul (N_le N hl.le) (N_le N hl) (by positivity) (by positivity)
  · intro l
    rw [card_RPl, nLa]
    refine (log_eight_leS CY N δ hS (eJ l).2).trans ?_
    have h6 : 8 ≤ C := by rw [hC]; linarith
    calc 8 * N.sc.L ≤ 8 * N.La := by linarith
      _ ≤ C * N.La := mul_le_mul_of_nonneg_right h6 (by linarith)
  · intro l τ
    rw [hR.sumNu, nLa]
    refine (log_nu_leS CY N δ hS (eJ l).2 τ).trans ?_
    have h6 : 5 ≤ C := by rw [hC]; linarith
    calc 5 * N.sc.L ≤ 5 * N.La := by linarith
      _ ≤ C * N.La := mul_le_mul_of_nonneg_right h6 (by linarith)
  · rw [nL, Real.log_mul (by positivity) (by positivity)]
    have b0 := (hS.2.1 0).2
    have b1 := (hS.2.1 1).2
    have h6 : 2 * max CY 0 + 2 ≤ C := by rw [hC]; linarith
    have c0 : CY * N.sc.L ≤ max CY 0 * N.sc.L := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    have c1 : 2 ≤ 2 * N.sc.L := by linarith
    calc _ ≤ (2 * max CY 0 + 2) * N.sc.L := by linarith
      _ ≤ C * N.sc.L := mul_le_mul_of_nonneg_right h6 (by linarith)
  · refine hP _ fun l v => ?_
    rw [kernelBound_wt N δ T CK _ (wt v) (h1 v) lo _]
    have hf0 : (N.R.f : ℝ) ≠ 0 := by linarith
    have e : (N.R.f : ℝ) * ((N.R.N (eJ l).1 : ℝ) * (N.R.N ((eJ l).1 + 1) : ℝ)) * ((∑ a, wt v a * lt a) / N.R.f) =
        ∑ a, wt v a * ((N.R.N (eJ l).1 : ℝ) * (N.R.N ((eJ l).1 + 1) : ℝ) * lt a) := by
      simp only [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      field_simp
    unfold Formalism.DimensionVariation.liftedMapLogSize kernelBound_sq
    simp only [hR.phNu, hR.sumNu, card_RPl, Nat.add_sub_cancel]
    rw [e]
    ring

set_option maxHeartbeats 2000000 in

theorem kerSide_chainS : ∀ CY : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (N : NumDatum) (X : Fields) [IsTotallyComplex X.K] (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (B : Base D D.host.ccK dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) (b : I.β (N.R.m - 2 + 1)) (hY : YbHyp (R := N.R) sel mu cst I u (N.R.m - 2) b) (hK : KerEquivC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch)) (hF : ∀ j, (chF W sel mu I u j).Ok) (hE : (evGSD W Ch sel mu (rPsymF Ch) u).Ok) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)), HostTie N s Pr → WeightTie N W pl u δ → CharTie N s W Ch G sel → AnalyticTie D dl χ cD → mu = 1 → cst.sharp = true → I.Ok Ch sel mu cst G (N.R.m - 2) → FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → Sizes Pr W N.sc.a → GlobalTheory.Core.Ht2.SizeRowsS CY N δ → Reads N eJ δ (Pr.T u) R → KerSide R (InfinitePlace X.K) C (FactorBounds (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) fun l => (eJ l).1) := by
  intro CY
  obtain ⟨CK, hCK, hfac⟩ := GlobalTheory.T.norms_matrixSteps_coupledFactor_bounded_anyLevelPrime (GlobalTheory.Proof.WeightSequenceEntries.blockBound_iff.1 GlobalTheory.JetBlock.blockBound) GlobalTheory.T.normalisedFamily_eq_tensorPower_vacuum
    GlobalTheory.T.normalisedFamily_nonzeroThetaVectors_numberField GlobalTheory.T.normalisedFamily_periodLattice_properties_hold GlobalTheory.T.cosetIndicatorThetaRefinement_proof GlobalTheory.T.meanLogPeriod_chowlaSelberg
  obtain ⟨Cc, hCc, hcl⟩ := GlobalTheory.ChainClassNumbersS.classNumbers_leS
  obtain ⟨Ci, hCi, hidx⟩ := GlobalTheory.T.card_matrixStep_indices_le_exp
  obtain ⟨Cy, hCy, hyb⟩ := GlobalTheory.CouplingCosetsS.ncard_ybSet_le
  obtain ⟨Ct, hth⟩ := GlobalTheory.T.normalisedFamily_normBound_absoluteConstant
  have hP := GlobalTheory.T.meanLogPeriod_chowlaSelberg
  have hV := GlobalTheory.T.normalisedFamily_nonzeroThetaVectors_numberField
  refine ⟨CK + 2 * (Cc + Ci + Cy) + 2 * max Ct 0 + 20 + 2 * max CY 0, by positivity, ?_⟩
  intro D N X _ s Pr W Ch G sel Sg mu cst I dl B χ cD pl u δ b hY hK hF hE J _ eJ R h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hR
  have H : GlobalTheory.Core.Ht2.HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ := ⟨h1, h2, h3, h4, h5, h6, h7, h9, h10⟩
  obtain ⟨trd, tv, tL, tOm, tf, -, tE, -, tcc⟩ := GlobalTheory.T.numDatum_numbers_eq_host_of_compatible D N X s Pr h1
  obtain ⟨-, -, -, -, hpsi, hadm, hX, hs, -, hPr, -, -, hg, -⟩ := id h1
  have hcrv : StandardLatticesGL3.Crv D D.host.ccK dl := ⟨tcc, h4.1⟩
  have hYf := GlobalTheory.T.kernelConstant_exponents_finite D B.γ₀ B.kc
  have hVe : B.VecP χ := hV D _ dl B χ hadm hpsi tcc h4.1 h4.2.1 hYf
  have hev : ∀ l, Even (N.R.N l) := fun l => by
    unfold Ranks.N
    exact N.R.k_even.add ((N.R.t_odd.add_one).mul_left l)
  have hm := N.R.two_le_m
  have hU : 0 ≤ errUnit N (Pr.T u) := by
    have h0 : (1 : ℝ) ≤ N.g 0 := by exact_mod_cast (N.g_prime 0).one_lt.le
    have h1' : (1 : ℝ) ≤ N.g 1 := by exact_mod_cast (N.g_prime 1).one_lt.le
    have h2' : (1 : ℝ) ≤ Pr.T u := by exact_mod_cast (hPr.T_prime u).one_lt.le
    have h3' : 0 ≤ Real.log ((N.g 0 : ℝ) * N.g 1 * Pr.T u) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h0 h1') h2')
    unfold errUnit
    positivity
  obtain ⟨hc1, -, hc3⟩ := hcl CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have m1 : Real.exp (Cc * errUnit N (Pr.T u)) ≤ Real.exp ((Cc + Ci + Cy) * errUnit N (Pr.T u)) := by
    gcongr; linarith
  have m2 : Real.exp (Ci * errUnit N (Pr.T u)) ≤ Real.exp ((Cc + Ci + Cy) * errUnit N (Pr.T u)) := by
    gcongr; linarith
  have m3 : Real.exp (Cy * errUnit N (Pr.T u)) ≤ Real.exp ((Cc + Ci + Cy) * errUnit N (Pr.T u)) := by
    gcongr; linarith
  have hh : ∀ l ≤ N.R.m, (classNumberAt W Ch sel mu I u l : ℝ) ≤ Real.exp ((Cc + Ci + Cy) * errUnit N (Pr.T u)) := by
    intro l hl
    refine le_trans ?_ m1
    unfold classNumberAt
    split_ifs with h
    · exact hc3
    · rw [← Nat.le_floor_iff (Real.exp_pos _).le]
      exact Finset.sup_le fun b _ => Nat.le_floor (hc1 l hl b)
  have hn : ∀ l ≤ N.R.m, (indexCount sel mu cst I l : ℝ) ≤ Real.exp ((Cc + Ci + Cy) * errUnit N (Pr.T u)) := by
    intro l hl
    unfold indexCount
    split_ifs with h h'
    · rw [Nat.cast_one]
      exact Real.one_le_exp (by positivity)
    · refine le_trans (hyb CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H _ ?_).1 m3
      unfold NumDatum.Nm Ranks.N
      gcongr
    · exact le_trans (hidx CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H l (by omega)) m2
  obtain ⟨M, hfd, hM⟩ : ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ThetaFieldData B cD s.σ₀ N.R M := by
    refine GlobalTheory.T.exists_numberField_containing_coefficientData D _ dl B cD X.K s.σ₀ N.R hcrv h4.2.2 fun i _ => ?_
    obtain ⟨hAdm, hbase⟩ := GlobalTheory.T.normalisedFamily_standardLattices_eq_baseVector D _ dl B χ h4.2.1 hVe _ _ (hev i) (hev (i + 1))
    rw [← hbase]
    exact (hVe _ _ _ _ hAdm).2.2
  haveI := hfd
  have hfac := fun ρ => hfac CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H B b hY hK hF hE h8 M hM ρ
  obtain ⟨wt, w0, w1, wup, wmean⟩ := GlobalTheory.PlaceWeights.exists_weights X.K s.σ₀ M hM.1
  choose lt hlt using GlobalTheory.T.log_norm_conj_vacuum_eq_rank_product_mul D dl B χ cD X.K s.σ₀ N.R M hadm hpsi tcc h4.1 h4.2.1 hVe hM
  have hmean : (∑ ρ, lt ρ) / (Module.finrank ℚ M : ℝ) ≤ max Ct 0 * N.R.f * (2 * N.sc.L) := by
    obtain ⟨hAdm, hbase⟩ := GlobalTheory.T.normalisedFamily_standardLattices_eq_baseVector D _ dl B χ h4.2.1 hVe _ _ (hev 0) (hev 1)
    have hco : TaylorLogMetric.CoefIn D (B.thZero (N.R.N 0) (N.R.N 1)) M := hM.2.2.2 0 (by omega)
    have hL0 : 0 ≤ N.sc.L := (Real.rpow_pos_of_pos (by linarith [N.sc.one_lt_alt]) _).le
    have hLs : Real.log D.host.v + |TaylorLogMetric.logDerivativeAtOne D| ≤ 2 * N.sc.L := by
      have g1 := h10.1.1
      have g2 := h10.1.2.2.2.2
      rw [← tv, ← tL]
      have g3 : 0 < N.rd := lt_of_lt_of_le one_pos (one_le_rd N)
      have g4 : Real.log N.v ≤ Real.log N.rd := Real.log_le_log (by unfold NumDatum.v; positivity) (by unfold NumDatum.v; linarith)
      linarith
    have h5' := (hth D _ dl B χ hadm hpsi tcc h4.1 h4.2.1 hYf).2.1 _ hLs _ _ _ _ hAdm M hM.2.1 (by rwa [hbase])
    rw [hbase, tf] at h5'
    have e : (∑ ρ : M →ₐ[ℚ] ℂ, logThAt B M ρ (N.R.N 0) (N.R.N 1)) / (Module.finrank ℚ M : ℝ) =
        ((N.R.N 0 : ℝ) * (N.R.N 1 : ℝ)) * ((∑ ρ, lt ρ) / (Module.finrank ℚ M : ℝ)) := by
      simp only [fun ρ => hlt ρ 0 (by omega : 0 < N.R.m)]
      rw [← Finset.mul_sum]
      ring
    have hpos : (0 : ℝ) < (N.R.N 0 : ℝ) * (N.R.N 1 : ℝ) := by
      have hk := N.R.m_add_three_le_k
      have a0 : 0 < N.R.N 0 := by unfold Ranks.N; omega
      have a1 : 0 < N.R.N 1 := by unfold Ranks.N; omega
      positivity
    have h6 : ((N.R.N 0 : ℝ) * (N.R.N 1 : ℝ)) * ((∑ ρ, lt ρ) / (Module.finrank ℚ M : ℝ)) ≤
        ((N.R.N 0 : ℝ) * (N.R.N 1 : ℝ)) * (max Ct 0 * N.R.f * (2 * N.sc.L)) := by
      rw [← e]
      refine le_trans h5' ?_
      calc _ ≤ max Ct 0 * N.R.f * (N.R.N 0 : ℝ) * (N.R.N 1 : ℝ) * (2 * N.sc.L) := by
            gcongr
            exact le_max_left _ _
        _ = _ := by ring
    exact le_of_mul_le_mul_left h6 hpos
  refine kerSide_of_meansS N δ (Pr.T u) (hPr.T_prime u).two_le CY h10 eJ R hR CK (Cc + Ci + Cy) (max Ct 0) (Module.finrank ℚ M : ℝ) hCK
    (by positivity) (le_max_right _ _) wt w1 wmean (fun ρ z => logOmAt B cD M ρ (s.iT (pl z))) lt ?_ hmean
    (classNumberAt W Ch sel mu I u) (indexCount sel mu cst I) hh hn _ ?_
  · intro z
    rw [tOm]
    exact (GlobalTheory.T.mean_logMetric_generator_eq_meanPeriod D _ dl cD hcrv (hP D _ dl tcc h4.1) h4.2.2).2 M hM.2.1 hM.2.2.1 _
  · intro t ht
    refine factorBounds_of_weights _ hm rfl eJ (fun ρ => placeUnder s.σ₀ hM.1 ρ) wt w0 w1 wup
      (fun ρ j => liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ j)
      (fun i v φ => GlobalTheory.ColumnFamilyMetric.famIpAt_nonneg X Pr N.R W sel Sg mu I u i (hF i) v φ)
      (fun a i hi => (hfac a).1 i hi) (fun a => (hfac a).2) t fun l v => ?_
    rw [ht]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    unfold liftBound_sq
    simp only [Nat.add_sub_cancel]
    rw [hlt ρ _ (eJ l).2]

end GlobalTheory.KernelHalfS
end

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelHalf_chainNumbers_any_levelPrime : ∀ CY : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (N : NumDatum) (X : Fields) [IsTotallyComplex X.K] (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (B : Base D D.host.ccK dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) (b : I.β (N.R.m - 2 + 1)) (hY : YbHyp (R := N.R) sel mu cst I u (N.R.m - 2) b) (hK : KerEquivC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch)) (hF : ∀ j, (chF W sel mu I u j).Ok) (hE : (evGSD W Ch sel mu (rPsymF Ch) u).Ok) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)), HostTie N s Pr → WeightTie N W pl u δ → CharTie N s W Ch G sel → AnalyticTie D dl χ cD → mu = 1 → cst.sharp = true → I.Ok Ch sel mu cst G (N.R.m - 2) → FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → Sizes Pr W N.sc.a → GlobalTheory.Core.Ht2.SizeRowsS CY N δ → Reads N eJ δ (Pr.T u) R → KerSide R (InfinitePlace X.K) C (FactorBounds (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) fun l => (eJ l).1) := by
  atlas_forward_decl GlobalTheory.KernelHalfS.kerSide_chainS
end

section
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ColRows.LastSideProof

theorem lastSide_of_logT_le : ∀ (CY CT : ℝ) (N : NumDatum) (X : Fields) (Pr : Primes X) (W : Wts X Pr.Word N.R) (pl : RPl N.R ≃ X.Tau)
    (u : Pr.Word) (δ : Code N) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)),
    WeightTie N W pl u δ → Sizes Pr W N.sc.a → GlobalTheory.Core.Ht2.SizeRowsS CY N δ → Real.log (Pr.T u : ℝ) ≤ CT * N.R.m * N.sc.L →
    1 ≤ Pr.T u → Reads N eJ δ (Pr.T u) R → LastSide R CT (lastLog W u) := by
  intro CY CT N X Pr W pl u δ J _ eJ R hWT hS hSR hlogT hT hR
  obtain ⟨C, hC⟩ := GlobalTheory.BranchLogBound.orthNormLogBound
  have hW : W.Ok := hWT.1
  have hk := N.R.m_add_three_le_k
  have hm := N.R.two_le_m
  obtain ⟨hL, ha, -, -, hmR, -, hkR, hNn, hSc, hη, hb', -⟩ := hR.nums
  obtain ⟨-, -, -, -, -, hnodes, hcloud, -, hbT, hoff⟩ := id hSR
  have hNq : ((N.Nm : ℕ) : ℝ) = (N.R.k : ℝ) + (N.R.m : ℝ) * ((N.R.t : ℝ) + 1) := by
    unfold NumDatum.Nm Ranks.N; push_cast; ring

  let lam1 : RPl N.R → ℝ := fun z => (ext (W.lamTrue u N.R.m (pl z)) 0 : ℝ)
  let D0 : RPl N.R → ℝ := fun z => ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ)
  let D1 : RPl N.R → ℝ := fun z =>
    ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ)
  let logc : RPl N.R → ℝ := fun z => (R.Nn - 1) * D1 z * Real.log (2 * R.a)
  let logxi : RPl N.R → ℝ := fun _ => R.Nn * (R.Nn - 1) / 2 * Real.log (2 * R.a)
  let bT : RPl N.R → ℝ := fun z => ((N.bT z.2 : ℚ) : ℝ)

  have hrow : ∀ z, (W.hc u (pl z)).v = (N.hc z).v ∧ (W.hc u (pl z)).b = (N.hc z).b ∧ (W.hc u (pl z)).e = (N.hc z).e := fun z =>
    ⟨congrArg RowPar.v (hWT.2.2 z).1, congrArg RowPar.b (hWT.2.2 z).1, congrArg RowPar.e (hWT.2.2 z).1⟩
  have hu0 : ∀ z, (W.hc u (pl z)).u ⟨0, by omega⟩ = (N.hc z).u ⟨0, by omega⟩ := fun z =>
    ((hWT.2.2 z).2 _).trans (uW_first N δ z _)
  have hul : ∀ z, (W.hc u (pl z)).u ⟨N.R.k - 1, by omega⟩ = (N.hc z).u ⟨N.R.k - 1, by omega⟩ := fun z =>
    ((hWT.2.2 z).2 _).trans (uW_last N δ z _)
  have hlam1 : ∀ z, lam1 z = (((N.hc z).u ⟨0, by omega⟩ : ℚ) : ℝ) - ((N.R.k : ℝ) - 1) / 2 -
      (N.R.m : ℝ) * (((N.R.t : ℝ) + 1) / 2) := by
    intro z
    have h := congrArg (fun q : ℚ => (q : ℝ)) (ext_lam_lo W u (pl z) 0 (by omega))
    rw [hu0 z] at h
    push_cast at h
    show (ext (W.lamTrue u N.R.m (pl z)) 0 : ℝ) = _
    rw [h]; ring
  have hsumB : ∀ z, ((∑ B ∈ Finset.range N.R.m, ((RowPar.of (W.hc u (pl z))).eAt B - (RowPar.of (W.hc u (pl z))).bAt B -
      ((N.R.t : ℚ) + 1) / 2) : ℚ) : ℝ) ≤ (N.R.m : ℝ) * N.eta := by
    intro z
    push_cast
    have : ∀ B ∈ Finset.range N.R.m, (((RowPar.of (W.hc u (pl z))).eAt B : ℚ) : ℝ) - (((RowPar.of (W.hc u (pl z))).bAt B : ℚ) : ℝ) -
        ((N.R.t : ℝ) + 1) / 2 ≤ N.eta := by
      intro B hB
      rw [Finset.mem_range] at hB
      rw [RowPar.eAt_of _ hB, RowPar.bAt_of _ hB, (hrow z).2.1, (hrow z).2.2]
      have h1 := hnodes z ⟨B, hB⟩ ⟨B, hB⟩
      have h2 := neg_abs_le ((((N.hc z).b ⟨B, hB⟩ - (N.hc z).e ⟨B, hB⟩ : ℚ) : ℝ))
      push_cast at h1 h2
      have ht : (0 : ℝ) ≤ N.R.t := Nat.cast_nonneg _
      linarith
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hD0 : ∀ z, D0 z ≤ N.Sc + (N.R.m : ℝ) * N.eta + (if z ∈ R.TT then bT z else 0) := by
    intro z
    have h := castQ (bottomRank_sum_le_two_mul_totalRank W hW u (pl z))
    push_cast at h
    have hB := hsumB z
    push_cast at hB
    have hv0 := hcloud z ⟨0, by omega⟩
    rw [← (hrow z).1] at hv0
    have hv0' : (((W.hc u (pl z)).v ⟨0, by omega⟩ : ℚ) : ℝ) ≤ N.Sc := hv0.2
    have hkR' : (5 : ℝ) ≤ N.R.k := by exact_mod_cast (by omega : 5 ≤ N.R.k)
    show ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) ≤ _
    split_ifs with htop
    · obtain ⟨h1, h2⟩ := (hR.tops z).1 htop
      have hbz : bT z = -(((N.hc z).u ⟨N.R.k - 1, by omega⟩ : ℚ) : ℝ) - ((N.R.k : ℝ) - 1) / 2 := by
        show ((N.bT z.2 : ℚ) : ℝ) = _
        obtain ⟨b, t⟩ := z
        simp only at h1
        subst h1
        unfold NumDatum.bT
        push_cast
        rfl
      rw [hbz, ← hul z]
      linarith
    · have hzero : (0 : ℚ) ≤ (N.hc z).v ⟨N.R.k - 2, by omega⟩ := (hcloud z ⟨N.R.k - 2, by omega⟩).1
      obtain ⟨hlast, -, -⟩ := hoff z (fun h => htop ((hR.tops z).2 h)) (by omega)
      have hl : (((W.hc u (pl z)).u ⟨N.R.k - 1, by omega⟩ : ℚ) : ℝ) = (((N.hc z).v ⟨N.R.k - 2, by omega⟩ : ℚ) : ℝ) - 1 / 2 := by
        rw [hul z, hlast]; push_cast; ring
      have hzero' : (0 : ℝ) ≤ (((N.hc z).v ⟨N.R.k - 2, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hzero
      rw [hl] at h
      linarith
  have hD1 : ∀ z, D1 z ≤ 3 * D0 z + N.Sc + N.eta := by
    intro z
    have h := castQ (dOne_le_place W hW u (pl z))
    push_cast at h
    have hv0 := (hcloud z ⟨0, by omega⟩).2
    have hvk := (hcloud z ⟨N.R.k - 2, by omega⟩).1
    rw [← (hrow z).1] at hv0 hvk
    have hvk' : (0 : ℝ) ≤ (((W.hc u (pl z)).v ⟨N.R.k - 2, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hvk
    have hu1 : (((W.hc u (pl z)).u ⟨1, by omega⟩ : ℚ) : ℝ) < (((W.hc u (pl z)).v ⟨0, by omega⟩ : ℚ) : ℝ) := by
      exact_mod_cast (W.hc u (pl z)).v_gt_u ⟨0, by omega⟩
    rw [RowPar.eAt_of _ (by omega : N.R.m - 1 < N.R.m), RowPar.eAt_of _ (by omega : 0 < N.R.m)] at h
    have hg := (W.hc u (pl z)).gap_be ⟨0, by omega⟩
    have hg' : ((((W.hc u (pl z)).b ⟨0, by omega⟩ : ℚ)) : ℝ) ≤ (((W.hc u (pl z)).e ⟨0, by omega⟩ : ℚ) : ℝ) := by
      have ht : (0 : ℚ) ≤ N.R.t := Nat.cast_nonneg _
      exact_mod_cast (by linarith : (W.hc u (pl z)).b ⟨0, by omega⟩ ≤ (W.hc u (pl z)).e ⟨0, by omega⟩)
    have hn := hnodes z ⟨0, by omega⟩ ⟨N.R.m - 1, by omega⟩
    rw [← (hrow z).2.1, ← (hrow z).2.2] at hn
    have hn' := neg_abs_le ((((W.hc u (pl z)).b ⟨0, by omega⟩ - (W.hc u (pl z)).e ⟨N.R.m - 1, by omega⟩ : ℚ) : ℝ))
    push_cast at hn hn'
    have hkR' : (5 : ℝ) ≤ N.R.k := by exact_mod_cast (by omega : 5 ≤ N.R.k)
    have hmt : (0 : ℝ) ≤ ((N.R.m : ℝ) - 1) * ((N.R.t : ℝ) + 1) := by
      have : (1 : ℝ) ≤ N.R.m := by exact_mod_cast (by omega : 1 ≤ N.R.m)
      have : (0 : ℝ) ≤ N.R.t := Nat.cast_nonneg _

      have : (0 : ℝ) ≤ N.R.t := Nat.cast_nonneg _
      nlinarith
    show ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) ≤
      3 * ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) + N.Sc + N.eta
    linarith
  refine ⟨bT, fun z => lam1 z - D0 z, lam1, D0, D1, logc, logxi, ?_, fun z => le_rfl, fun z => le_rfl, fun z => rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hI : (∀ τ, Br.Interlace (N_m_succ N.R) (W.lamTrue u N.R.m τ) (W.sgTrue τ)) ∧ ∀ τ, Br.SameShift (W.lamTrue u N.R.m τ) (W.sgTrue τ) :=
      ⟨fun τ => GlobalTheory.BranchMembers.interlace W hW u τ, fun τ => GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.members_sameShift W hW u τ⟩
    have hsp : ∀ τ, (((W.lamTrue u N.R.m τ).spread : ℤ) : ℝ) ≤ 2 * N.sc.a := fun τ => hS.spread_le u N.R.m le_rfl τ
    obtain ⟨-, hlog, -⟩ := hC X.Tau (N.R.N N.R.m) (N.R.N N.R.m - 1) (N_m_succ N.R) (fun τ => W.lamTrue u N.R.m τ) W.sgTrue
      hI.1 N.sc.a hsp
    have hA : lastLog W u = -((∑ τ, Br.nBr (W.lamTrue u N.R.m τ) (W.sgTrue τ) : ℤ) : ℝ) * Real.log (Pr.T u : ℝ) +
        Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.orthNormSq (N_m_succ N.R) (fun τ => W.lamTrue u N.R.m τ) W.sgTrue) := rfl
    have h0 : ∀ z, ext (W.lamTrue u N.R.m (pl z)) 0 = (W.lamTrue u N.R.m (pl z)).w ⟨0, N.R.N_pos N.R.m⟩ := fun z =>
      ext_of _ ⟨0, _⟩
    have hn : ((∑ τ, Br.nBr (W.lamTrue u N.R.m τ) (W.sgTrue τ) : ℤ) : ℝ) = ∑ z, (lam1 z - D0 z) := by
      rw [Int.cast_sum, ← Equiv.sum_comp pl]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [nBr_eq_sub (N_m_succ N.R)]
      show _ = ((ext (W.lamTrue u N.R.m (pl z)) 0 : ℤ) : ℝ) -
        ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ)
      rw [h0]
      push_cast
      rfl
    have hre : ∑ τ, (2 * (((N.R.N N.R.m : ℕ) : ℝ) - 1) *
          ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m τ) (W.sgTrue τ) : ℤ) : ℝ) +
          ((N.R.N N.R.m : ℕ) : ℝ) * (((N.R.N N.R.m : ℕ) : ℝ) - 1) / 2) * Real.log (2 * N.sc.a) =
        ∑ z, (2 * logc z + logxi z) := by
      rw [← Equiv.sum_comp pl]
      refine Finset.sum_congr rfl fun z _ => ?_
      show _ = 2 * ((R.Nn - 1) * ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) *
        Real.log (2 * R.a)) + R.Nn * (R.Nn - 1) / 2 * Real.log (2 * R.a)
      rw [hNn, ha]
      unfold NumDatum.Nm
      ring
    show lastLog W u ≤ -(∑ z, (lam1 z - D0 z) * R.logT) + ∑ z, (2 * logc z + logxi z)
    rw [hA, hn, hR.logT, ← Finset.sum_mul, ← hre]
    linarith
  · intro z hz
    obtain ⟨h1, h2⟩ := (hR.tops z).1 hz
    obtain ⟨b, t⟩ := z
    simp only at h1
    subst h1
    rw [hlam1, hR.aT t h2, hNn, hkR, hNq]
    unfold NumDatum.aT
    push_cast
    ring
  · intro z hz
    obtain ⟨-, hS1, -⟩ := hoff z (fun h => hz ((hR.tops z).2 h)) (by omega)
    have hv := (hcloud z ⟨0, by omega⟩).1
    have hv' : (0 : ℝ) ≤ (((N.hc z).v ⟨0, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hv
    rw [hlam1, hSc, hNn, hNq]
    push_cast at hS1
    linarith
  · intro z
    rw [hSc, hmR, hη]
    exact hD0 z
  · intro z
    rw [hSc, hη]
    exact hD1 z
  · intro z hz
    obtain ⟨h1, h2⟩ := (hR.tops z).1 hz
    obtain ⟨b, t⟩ := z
    simp only at h1
    subst h1
    rw [hb']
    exact (hbT t h2).2
  · rw [hR.logT]
    exact Real.log_nonneg (by exact_mod_cast hT)
  · rw [hR.logT, hmR, hL]
    exact hlogT

end GlobalTheory.ColRows.LastSideProof
end

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastMapHalf_recNums_of_log_levelPrime_le : ∀ (CY CT : ℝ) (N : NumDatum) (X : Fields) (Pr : Primes X) (W : Wts X Pr.Word N.R) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)), WeightTie N W pl u δ → Sizes Pr W N.sc.a → GlobalTheory.Core.Ht2.SizeRowsS CY N δ → Real.log (Pr.T u : ℝ) ≤ CT * N.R.m * N.sc.L → 1 ≤ Pr.T u → Reads N eJ δ (Pr.T u) R → LastSide R CT (lastLog W u) := by
  atlas_forward_decl GlobalTheory.ColRows.LastSideProof.lastSide_of_logT_le
end

section
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRowsTopS

theorem rowsBody_colFace : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (N : NumDatum) (X : Fields) [IsTotallyComplex X.K] (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (hX : X.Ok) (Bs : DefBase X.K) (Df : DefSide Bs) (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs N.R.r → X.K)) (mu : Bs.Tup → Tup X.F X.E X.K Sg) (cst : ∀ t, LocCst X (rowSG Pr sel (mu t))) (I : ∀ t, ChIdx X Pr N.R (QE sel (mu t : Chr X.F X.E X.K))) (hL : ∀ t, (I t).Ok Ch sel (mu t) (cst t) G (N.R.m - 2)) (hP : ∀ t, (mtildeGSD W Ch sel (mu t) (rPsymF Ch)).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (I t).β (N.R.m - 2 + 1)) (hY : ∀ t x, YbHyp (R := N.R) sel (mu t) (cst t) (I t) (wd x) (N.R.m - 2) (b t x)) (dl : ℂ) (B : Base D D.host.ccK dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (hK : ∀ t x, KerEquivC W Ch sel (mu t) (cst t) (I t) (ambOf s B χ cD) (wd x) (N.R.m - 2) (b t x) (hY t x) (rPsymF Ch)) (hF : ∀ t x j, (chF W sel (mu t) (I t) (wd x) j).Ok) (hE : ∀ x, (evGSD W Ch sel (mu Bs.μ0) (rPsymF Ch) (wd x)).Ok) (ev : ∀ t, (Fin (Df.nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg (rPsymF Ch)) (pl : RPl N.R ≃ X.Tau) (x : Mem) (δ : Code N) (eJ : Bs.J ≃ Fin N.R.m) (R : RecNums Bs.J (RPl N.R)), HostTie N s Pr → WeightTie N W pl (wd x) δ → CharTie N s W Ch G sel → AnalyticTie D dl χ cD → mu Bs.μ0 = 1 → (cst Bs.μ0).sharp = true → FieldOfDefinition W sel (mu Bs.μ0) (cst Bs.μ0) (wd x) (ambOf s B χ cD) → Sizes Pr W N.sc.a → GlobalTheory.Core.Ht2.SizeRowsS CY N δ → Real.log (Pr.T (wd x) : ℝ) ≤ CT * N.R.m * N.sc.L → Reads N eJ δ (Pr.T (wd x)) R → C0 ≤ R.Ch → (∀ v : InfinitePlace X.K, ((Df.HV Bs.μ0).map v.embedding).PosDef) → (∀ X0, IsFrames Df X0 → ∀ v F, ((mtildeGSD W Ch sel (mu Bs.μ0) (rPsymF Ch)).ipAt (hP Bs.μ0) v ((ev Bs.μ0 F).1).1 ((ev Bs.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K (Fin (Df.nV Bs.μ0))) X0 v F ^ 2) → RowsBody (colFace hX Df Xg mu cst I hL hP Mem wd b hY (kerRec mu cst I wd b hY (ambOf s B χ cD) hK) hF ev) x (memQ (A := kerRec mu cst I wd b hY (ambOf s B χ cD) hK) (hF := hF) hE (x := x)) (colsIn W Ch hX sel (mu Bs.μ0) (cst Bs.μ0) (I Bs.μ0) (hL Bs.μ0) (wd x)) R ∧ ∀ v, IsUnit ((MramH W Ch hX (wd x)).X v).det := by
  intro CY CT hCT
  obtain ⟨C, hC, hker⟩ := GlobalTheory.T.kernelHalf_chainNumbers_any_levelPrime CY
  refine ⟨max (2 * (16 + CT)) (max (6 * C + 1 + 2 * C * C) (4 * C * (CT + C))), ?_⟩
  intro D N X _ s Pr W Ch G sel Sg hX Bs Df Xg mu cst I hL hP Mem wd b hY dl B χ cD hK hF hE ev pl x δ eJ R
    hHost hWt hChar hAn hmu hsharp hFD hS hR hlogT hRd hC0 hpos hev
  have hPr : Pr.Ok := hHost.2.2.2.2.2.2.2.2.2.1
  have hT : 1 ≤ Pr.T (wd x) := (hPr.T_prime _).one_le
  have hk := hker D N X s Pr W Ch G sel Sg (mu Bs.μ0) (cst Bs.μ0) (I Bs.μ0) dl B χ cD pl (wd x) δ (b Bs.μ0 x) (hY Bs.μ0 x)
    (hK Bs.μ0 x) (hF Bs.μ0 x) (hE x) Bs.J eJ R hHost hWt hChar hAn hmu hsharp (hL Bs.μ0) hFD hS hR hRd
  have hl := GlobalTheory.T.lastMapHalf_recNums_of_log_levelPrime_le CY CT N X Pr W pl (wd x) δ Bs.J eJ R hWt hS hR hlogT hT hRd
  obtain ⟨hn, hA, hsz⟩ := GlobalTheory.ColRows.exists_htNums_of_kerSide_lastSide Bs.J (RPl N.R) (InfinitePlace X.K) R C CT _ _ hC hCT
    ((le_max_left _ _).trans hC0) (((le_max_left _ _).trans (le_max_right _ _)).trans hC0)
    (((le_max_right _ _).trans (le_max_right _ _)).trans hC0) hk hl
  obtain ⟨X0, hX0⟩ := GlobalTheory.ColRows.exists_isFrames X.K Bs Df hpos
  obtain ⟨hdet, hiso⟩ := GlobalTheory.ColFirstIso.colsIn_isometry X hX Pr N.R W Ch sel Sg (mu Bs.μ0) (cst Bs.μ0) (I Bs.μ0) G _ (hL Bs.μ0)
    (wd x) (hF Bs.μ0 x 0) hmu
  have hint : ∀ τ, Br.Interlace (N_m_succ N.R) (W.lamTrue (wd x) N.R.m τ) (W.sgTrue τ) :=
    fun τ => GlobalTheory.BranchMembers.interlace W hWt.1 (wd x) τ
  have hsh : ∀ τ, Br.SameShift (W.lamTrue (wd x) N.R.m τ) (W.sgTrue τ) :=
    fun τ => GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.members_sameShift W hWt.1 (wd x) τ
  have hdat := GlobalTheory.ColRows.evGSD_datFramed X hX Pr N.R W Ch sel Sg (mu Bs.μ0) (rPsymF Ch) (wd x) (hE x)
  refine ⟨GlobalTheory.T.kerChain_matrices_with_norm_bounds X.K Bs Df (colFace hX Df Xg mu cst I hL hP Mem wd b hY (kerRec mu cst I wd b hY (ambOf s B χ cD) hK) hF ev) x
    (memQ (A := kerRec mu cst I wd b hY (ambOf s B χ cD) hK) (hF := hF) hE (x := x)) _
    (colPerL (hP Bs.μ0) Xg (wd x) (ev Bs.μ0)) (RPl N.R) R hn (fun l => (eJ l).1) X0 hdet hiso
    (fun i => GlobalTheory.FamilyFrames.famFramed_chF X hX Pr N.R W Ch sel Sg (mu Bs.μ0) (I Bs.μ0) (wd x) i (hF Bs.μ0 x i)) hdat
    (fun φ F => colPer_eq hX (hP Bs.μ0) Xg _ (hF Bs.μ0 x) (hE x) (hL Bs.μ0) (ev Bs.μ0) φ F) hX0 hsz ?_, hdet⟩
  intro v ψ F
  have hb := GlobalTheory.ColRowsTop.period_le GlobalTheory.BranchNorm.lastMapNorm hX hPr W Ch sel (mu Bs.μ0) hmu (rPsymF Ch) (wd x) hint hsh
    (hP Bs.μ0) (hE x) v ψ.1 (ev Bs.μ0 F).1.1
  rw [hA]
  exact hb.trans (mul_le_mul_of_nonneg_left (hev X0 hX0 v F)
    (mul_nonneg (Real.exp_pos _).le (GlobalTheory.ColRowsTop.ipAt_nonneg_of_datFramed hdat v ψ)))

end GlobalTheory.ColRowsTopS
end

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnsMemberRows_of_logLevel_le : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (N : NumDatum) (X : Fields) [IsTotallyComplex X.K] (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (hX : X.Ok) (Bs : DefBase X.K) (Df : DefSide Bs) (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs N.R.r → X.K)) (mu : Bs.Tup → Tup X.F X.E X.K Sg) (cst : ∀ t, LocCst X (rowSG Pr sel (mu t))) (I : ∀ t, ChIdx X Pr N.R (QE sel (mu t : Chr X.F X.E X.K))) (hL : ∀ t, (I t).Ok Ch sel (mu t) (cst t) G (N.R.m - 2)) (hP : ∀ t, (mtildeGSD W Ch sel (mu t) (rPsymF Ch)).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (I t).β (N.R.m - 2 + 1)) (hY : ∀ t x, YbHyp (R := N.R) sel (mu t) (cst t) (I t) (wd x) (N.R.m - 2) (b t x)) (dl : ℂ) (B : Base D D.host.ccK dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (hK : ∀ t x, KerEquivC W Ch sel (mu t) (cst t) (I t) (ambOf s B χ cD) (wd x) (N.R.m - 2) (b t x) (hY t x) (rPsymF Ch)) (hF : ∀ t x j, (chF W sel (mu t) (I t) (wd x) j).Ok) (hE : ∀ x, (evGSD W Ch sel (mu Bs.μ0) (rPsymF Ch) (wd x)).Ok) (ev : ∀ t, (Fin (Df.nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg (rPsymF Ch)) (pl : RPl N.R ≃ X.Tau) (x : Mem) (δ : Code N) (eJ : Bs.J ≃ Fin N.R.m) (R : RecNums Bs.J (RPl N.R)), HostTie N s Pr → WeightTie N W pl (wd x) δ → CharTie N s W Ch G sel → AnalyticTie D dl χ cD → mu Bs.μ0 = 1 → (cst Bs.μ0).sharp = true → FieldOfDefinition W sel (mu Bs.μ0) (cst Bs.μ0) (wd x) (ambOf s B χ cD) → Sizes Pr W N.sc.a → GlobalTheory.Core.Ht2.SizeRowsS CY N δ → Real.log (Pr.T (wd x) : ℝ) ≤ CT * N.R.m * N.sc.L → Reads N eJ δ (Pr.T (wd x)) R → C0 ≤ R.Ch → (∀ v : InfinitePlace X.K, ((Df.HV Bs.μ0).map v.embedding).PosDef) → (∀ X0, IsFrames Df X0 → ∀ v F, ((mtildeGSD W Ch sel (mu Bs.μ0) (rPsymF Ch)).ipAt (hP Bs.μ0) v ((ev Bs.μ0 F).1).1 ((ev Bs.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K (Fin (Df.nV Bs.μ0))) X0 v F ^ 2) → RowsBody (colFace hX Df Xg mu cst I hL hP Mem wd b hY (kerRec mu cst I wd b hY (ambOf s B χ cD) hK) hF ev) x (memQ (A := kerRec mu cst I wd b hY (ambOf s B χ cD) hK) (hF := hF) hE (x := x)) (colsIn W Ch hX sel (mu Bs.μ0) (cst Bs.μ0) (I Bs.μ0) (hL Bs.μ0) (wd x)) R ∧ ∀ v, IsUnit ((MramH W Ch hX (wd x)).X v).det := by
  atlas_forward_decl GlobalTheory.ColRowsTopS.rowsBody_colFace
end

section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ColRows.NumReads

open Formalism.LatticeIndexTer (ph)

theorem ph_zero : ph 0 = 0 := by simp [ph]

theorem N_pred_le (N : NumDatum) (j : ℕ) (hj : j < N.R.m) : N.R.N ((j + 1) - 1) ≤ N.Nm := by
  unfold NumDatum.Nm Ranks.N
  rw [Nat.add_sub_cancel]
  have := Nat.mul_le_mul_right (N.R.t + 1) hj.le
  omega

theorem ofNum_reads : ∀ (N : NumDatum) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (δ : Code N) (T : ℕ)
    (Nc lam0 C0 ce Ch Sw C1 : ℝ) (H : N.NumFacts δ Nc lam0 C0 ce Ch Sw C1),
    Reads N eJ δ T (RecNums.ofNum N eJ δ T Nc lam0 C0 ce Ch Sw C1 H) := by
  intro N J _ eJ δ T Nc lam0 C0 ce Ch Sw C1 H
  refine ⟨?_, ?_, rfl, ?_, ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · intro z
    exact N.mem_topsPl z
  · intro t _
    rfl
  · intro j z
    have hle := N_pred_le N (eJ j).1 (eJ j).2
    show ∑ i : Fin N.Nm, ph (N.nuPad δ ((eJ j).1 + 1) z i) = _
    unfold NumDatum.nuPad
    have e : ∀ i : Fin N.Nm, ph (if i.1 < N.R.N ((eJ j).1 + 1 - 1) then ((N.nu δ ((eJ j).1 + 1) z i.1 : ℚ) : ℝ) else 0) =
        (if i.1 < N.R.N ((eJ j).1 + 1 - 1) then ph ((N.nu δ ((eJ j).1 + 1) z i.1 : ℚ) : ℝ) else 0) := by
      intro i
      split_ifs
      · rfl
      · exact ph_zero
    rw [Finset.sum_congr rfl (fun i _ => e i),
      NumDatum.sum_pad (fun i => ph ((N.nu δ ((eJ j).1 + 1) z i : ℚ) : ℝ)) hle, Nat.add_sub_cancel]
  · intro j z
    have hle := N_pred_le N (eJ j).1 (eJ j).2
    show ∑ i : Fin N.Nm, N.nuPad δ ((eJ j).1 + 1) z i = _
    unfold NumDatum.nuPad NumDatum.nuAbs
    rw [NumDatum.sum_pad (fun i => ((N.nu δ ((eJ j).1 + 1) z i : ℚ) : ℝ)) hle]
    push_cast
    rfl

end GlobalTheory.ColRows.NumReads
end

section
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRows

theorem rowsBody_of_kerTies : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) [IsTotallyComplex t.X.K] (W : Formalism.L2.Col.Wts t.X t.Pr.Word D.R) (Del h0 : ℕ) (hX : t.X.Ok) (Bs : DefBase t.X.K) (Df : DefSide Bs) (Xg : Finset (Formalism.L2.Col.G0 t.X.E t.Pr.vGs D.R.r → t.X.K)) (tup : Bs.Tup → D.what₂.Tup) (hP : ∀ τ, (mtildeGSD W t.Ch t.sel (t.tup (tup τ)) (rPsymF (R := D.R) t.Ch)).Ok) (b : ∀ τ, D.what₂.Word → (t.idx (tup τ)).β (t.m2 + 1)) (hY : ∀ τ x, YbHyp (R := D.R) t.sel (t.tup (tup τ)) (t.cst (tup τ)) (t.idx (tup τ)) (t.word x) t.m2 (b τ x)) (hK : ∀ τ x, KerEquivC W t.Ch t.sel (t.tup (tup τ)) (t.cst (tup τ)) (t.idx (tup τ)) t.amb (t.word x) t.m2 (b τ x) (hY τ x) (rPsymF (R := D.R) t.Ch)) (hF : ∀ τ x j, (chF W t.sel (t.tup (tup τ)) (t.idx (tup τ)) (t.word x) j).Ok) (hE : ∀ x, (evGSD W t.Ch t.sel (t.tup (tup Bs.μ0)) (rPsymF (R := D.R) t.Ch) (t.word x)).Ok) (ev : ∀ τ, (Fin (Df.nV τ) → t.X.K) →ₗ[t.X.K] V0X W t.Ch t.sel (t.tup (tup τ)) Xg (rPsymF (R := D.R) t.Ch)) (u : D.what₂.Word) (eJ : Bs.J ≃ Fin D.R.m) (Nc lam0 c0 ce Ch Sw C1 : ℝ) (H : (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) Nc lam0 c0 ce Ch Sw C1), tup Bs.μ0 = D.what₂.mu0 → KerTies t W Del h0 → KerSizes t W Del h0 CY CT → C0 ≤ Ch → (∀ v : InfinitePlace t.X.K, ((Df.HV Bs.μ0).map v.embedding).PosDef) → (∀ X0, IsFrames Df X0 → ∀ v F, ((mtildeGSD W t.Ch t.sel (t.tup (tup Bs.μ0)) (rPsymF (R := D.R) t.Ch)).ipAt (hP Bs.μ0) v ((ev Bs.μ0 F).1).1 ((ev Bs.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun t.X.K (Fin (Df.nV Bs.μ0))) X0 v F ^ 2) → RowsBody (colFace hX Df Xg (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) (fun τ => t.idx_ok (tup τ)) hP D.what₂.Word t.word b hY (kerRec (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) t.word b hY t.amb hK) hF ev) u (memQ (A := (kerRec (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) t.word b hY t.amb hK)) (hF := hF) hE (x := u)) (colsIn W t.Ch hX t.sel (t.tup (tup Bs.μ0)) (t.cst (tup Bs.μ0)) (t.idx (tup Bs.μ0)) (t.idx_ok (tup Bs.μ0)) (t.word u)) (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) (D.mem u).A.T Nc lam0 c0 ce Ch Sw C1 H) ∧ ∀ v, IsUnit ((MramH W t.Ch hX (t.word u)).X v).det := by
  intro CY CT hCT
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.columnsMemberRows_of_logLevel_le CY CT hCT
  refine ⟨C0, fun D L hT Gi Gl K Y cX ex t _ W Del h0 hX Bs Df Xg tup hP b hY hK hF hE ev u eJ Nc lam0 c0 ce Ch Sw C1 H hmu hTi hS hC hPD hFr => ?_⟩
  obtain ⟨pl, hpl⟩ := hTi.wts
  have hmu0 : t.tup (tup Bs.μ0) = 1 := hmu ▸ hTi.mu0
  have hsh : (t.cst (tup Bs.μ0)).sharp = true := by rw [hmu]; exact hTi.sharp
  have hfld : FieldOfDefinition W t.sel (t.tup (tup Bs.μ0)) (t.cst (tup Bs.μ0)) (t.word u) t.amb := by
    rw [hmu]; exact hTi.fld u
  have hlog : Real.log (t.Pr.T (t.word u) : ℝ) ≤ CT * D.R.m * L.sc.L := by rw [t.T_rec u]; exact hS.logT u
  have hRd : Reads (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) (t.Pr.T (t.word u))
      (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) (D.mem u).A.T Nc lam0 c0 ce Ch Sw C1 H) := by
    rw [t.T_rec u]; exact NumReads.ofNum_reads _ _ eJ _ _ Nc lam0 c0 ce Ch Sw C1 H
  have hm2 := hTi.m2
  have hcc := t.cc_rec
  have hsz := hS.sizes
  have hrw := hS.what₂ u
  have hho := hTi.host
  have hch := hTi.chr
  have han := hTi.an
  have hwt := hpl u
  clear hTi hS hpl
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, B, χ, χ_ok, idl, idl_ok, χ_rec, cD, X, seam, seam_ok, Pr, pr_ok, g_rec, ChT, sel, S, word, T_rec, tupT, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  dsimp only at *
  subst hm2
  subst hcc
  exact hC0 D (ofRecord D L Del h0) X seam Pr W ChT glob sel S hX Bs Df Xg (fun τ => tupT (tup τ)) (fun τ => cst (tup τ))
    (fun τ => idx (tup τ)) (fun τ => idx_ok (tup τ)) hP D.what₂.Word word b hY δ B χ cD hK hF hE ev pl u (letterOf D L Del h0 u) eJ _
    hho hwt hch han hmu0 hsh hfld hsz hrw hlog hRd hC hPD hFr

end GlobalTheory.ColRows
end

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberRows_of_kernelDatum_sizes : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) [IsTotallyComplex t.X.K] (W : Formalism.L2.Col.Wts t.X t.Pr.Word D.R) (Del h0 : ℕ) (hX : t.X.Ok) (Bs : DefBase t.X.K) (Df : DefSide Bs) (Xg : Finset (Formalism.L2.Col.G0 t.X.E t.Pr.vGs D.R.r → t.X.K)) (tup : Bs.Tup → D.what₂.Tup) (hP : ∀ τ, (mtildeGSD W t.Ch t.sel (t.tup (tup τ)) (rPsymF (R := D.R) t.Ch)).Ok) (b : ∀ τ, D.what₂.Word → (t.idx (tup τ)).β (t.m2 + 1)) (hY : ∀ τ x, YbHyp (R := D.R) t.sel (t.tup (tup τ)) (t.cst (tup τ)) (t.idx (tup τ)) (t.word x) t.m2 (b τ x)) (hK : ∀ τ x, KerEquivC W t.Ch t.sel (t.tup (tup τ)) (t.cst (tup τ)) (t.idx (tup τ)) t.amb (t.word x) t.m2 (b τ x) (hY τ x) (rPsymF (R := D.R) t.Ch)) (hF : ∀ τ x j, (chF W t.sel (t.tup (tup τ)) (t.idx (tup τ)) (t.word x) j).Ok) (hE : ∀ x, (evGSD W t.Ch t.sel (t.tup (tup Bs.μ0)) (rPsymF (R := D.R) t.Ch) (t.word x)).Ok) (ev : ∀ τ, (Fin (Df.nV τ) → t.X.K) →ₗ[t.X.K] V0X W t.Ch t.sel (t.tup (tup τ)) Xg (rPsymF (R := D.R) t.Ch)) (u : D.what₂.Word) (eJ : Bs.J ≃ Fin D.R.m) (Nc lam0 c0 ce Ch Sw C1 : ℝ) (H : (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) Nc lam0 c0 ce Ch Sw C1), tup Bs.μ0 = D.what₂.mu0 → KerTies t W Del h0 → KerSizes t W Del h0 CY CT → C0 ≤ Ch → (∀ v : InfinitePlace t.X.K, ((Df.HV Bs.μ0).map v.embedding).PosDef) → (∀ X0, IsFrames Df X0 → ∀ v F, ((mtildeGSD W t.Ch t.sel (t.tup (tup Bs.μ0)) (rPsymF (R := D.R) t.Ch)).ipAt (hP Bs.μ0) v ((ev Bs.μ0 F).1).1 ((ev Bs.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun t.X.K (Fin (Df.nV Bs.μ0))) X0 v F ^ 2) → RowsBody (colFace hX Df Xg (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) (fun τ => t.idx_ok (tup τ)) hP D.what₂.Word t.word b hY (kerRec (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) t.word b hY t.amb hK) hF ev) u (memQ (A := (kerRec (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) t.word b hY t.amb hK)) (hF := hF) hE (x := u)) (colsIn W t.Ch hX t.sel (t.tup (tup Bs.μ0)) (t.cst (tup Bs.μ0)) (t.idx (tup Bs.μ0)) (t.idx_ok (tup Bs.μ0)) (t.word u)) (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) (D.mem u).A.T Nc lam0 c0 ce Ch Sw C1 H) ∧ ∀ v, IsUnit ((MramH W t.Ch hX (t.word u)).X v).det := by
  atlas_forward_decl GlobalTheory.ColRows.rowsBody_of_kerTies
end

section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRows

set_option maxHeartbeats 2000000 in

theorem rowsU_of_colPins : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) [IsTotallyComplex D.what₂.LL] (T : Formalism.L2.TiedDataSK ex) (P : RowSideFamily ex) (K : SquareIntegrableColumnsCompatible T P) (W : Formalism.L2.Col.Wts T.ker.X T.ker.Pr.Word D.R) (Del h0 : ℕ), ColPins K → HEq K.c.W W → KerTies T.ker W Del h0 → KerSizes T.ker W Del h0 CY CT → DV.NprimeDef D L → D.NuFull → (∀ u, 0 < (D.div.Nu u).rank) → ∀ (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (cf : ConvFace P.A3.fam3.base3) (Cl CHl : ℝ) (Pk : IndefPkgR P.A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 P.A3 P.P0 P.ψ0 P.Ps P.ψs K.c.face K.Sp Zsc) cf Cl CHl), Pk.Zs = P.Zs → ∀ (u : D.what₂.Word) (lam0 c0 ce Ch Sw C1 : ℝ) (H : (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 c0 ce Ch Sw C1) (w : (K.c.face Pk.Zs).Mem) (e : (Fin ((K.c.face Pk.Zs).a w) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V), HEq w u → C0 ≤ Ch → ∃ (ch : ColChain (K.c.face Pk.Zs) w) (Tc : ChainTie ch (K.c.memQ w)), FirstCols K.c.hE Tc ∧ ∃ (X0 : InfinitePlace D.what₂.LL → Matrix (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) ℂ) (_ : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = ((P.A3.side3 P.Ps P.ψs Pk.Zs).HV P.A3.fam3.base3.μ0).map v.embedding) (hn : HtNums (RecNums.ofNum (ofRecord D L Del h0) (Equiv.refl _) (letterOf D L Del h0 u) (D.mem u).A.T L.Nc lam0 c0 ce Ch Sw C1 H) (InfinitePlace D.what₂.LL)) (_ : ∀ v, Formalism.HN.opNormAt (Pi.basisFun D.what₂.LL (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm)) (Pi.basisFun D.what₂.LL (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hn.hPn) (cb : CBData ch.X ch.Kj), (∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v) ∧ (∀ v, IsUnit ((K.c.face Pk.Zs).Xc w v).det) ∧ 0 < (K.c.face Pk.Zs).a w ∧ Submodule.IsLattice D.what₂.LL (Cons.nuOf L u e) := by
  intro CY CT hCT
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.memberRows_of_kernelDatum_sizes CY CT hCT
  refine ⟨C0, ?_⟩
  intro D L hT Gi Gl Kc Y cX ex _ T P K W Del h0 hPins hW hKT hKS hN hNu hrk Zsc cf Cl CHl Pk hZs u lam0 c0 ce Ch Sw C1 H w e hwu hCh
  have hmu0 : P.I.tup P.A3.fam3.base3.μ0 = D.what₂.mu0 := P.tied.div.tup.mu0
  have hpos : ∀ v : InfinitePlace D.what₂.LL, (((P.A3.side3 P.Ps P.ψs Pk.Zs).HV P.A3.fam3.base3.μ0).map v.embedding).PosDef :=
    fun v => Formalism.L2.DIV.BlockDat.HV_pos (ℓ := P.A3.fam3.F.lvl P.Ps P.ψs) K.ok1.ok2.conj (K.ok1.ok2.what₂ _) K.ok1.ok2.irr v
  have hlat : Submodule.IsLattice D.what₂.LL (Cons.nuOf L u e) :=
    nuLat_comap_isLattice D L hN u ⟨(hNu u).1, (hNu u).2⟩ _ e
  have ha : 0 < (K.c.face Pk.Zs).a w := by
    have h := hrk u
    change 0 < Module.finrank D.what₂.LL (Submodule.span D.what₂.LL ((D.div.Nu u).L : Set (D.div.Nu u).V)) at h
    rw [(hNu u).2, finrank_top, ← e.finrank_eq, Module.finrank_fin_fun] at h
    exact h
  have hev := GlobalTheory.T.frames_tilde_gamma_values D L hT Gi Gl Kc Y cX ex T P K hPins
  rw [← hZs] at hev
  clear hPins hrk hNu
  obtain ⟨X, e', c, Sp, colTie, kerTie, wTie, lvTie, sgTie, v0, TU, xiVal, trIv, famEq, gEq, plEq, i0Eq, tEq, muTie, ok1⟩ := K
  obtain ⟨toS, ker, crd, crd_gram, crd_lat, ker_sharp, ker_frm⟩ := T
  obtain ⟨cc, cc_rec, cc_ok, δ, δ_ok, B, χ, χ_ok, idl, idl_ok, χ_rec, cD, kX, seam, seam_ok, kPr, pr_ok, g_rec, kCh, ksel, kS, kword, T_rec, ktup, Q_rec, kcst, kidx, km2, kglob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩ := ker
  obtain ⟨Pr, Rk, W', Ch', sel, Sg, hX, Lv, Xg, m2, Gc, mu, cst, Li, hL, hP, Mem, wd, b, hY, Am, hK, hF, hE, ev⟩ := c
  have hXe : kX = fieldsLL D X e' := kerTie.1
  subst hXe
  have hRk : Rk = D.R := kerTie.2.1
  subst hRk
  have hPr : Pr = kPr := eq_of_heq kerTie.2.2.1
  subst hPr
  have hChE : Ch' = kCh := eq_of_heq kerTie.2.2.2.1
  subst hChE
  have hsel : sel = ksel := eq_of_heq kerTie.2.2.2.2.1
  subst hsel
  have hSg : Sg = kS := eq_of_heq kerTie.2.2.2.2.2.1
  subst hSg
  have hmu : mu = fun t => ktup (P.I.tup t) := eq_of_heq kerTie.2.2.2.2.2.2.1
  subst hmu
  have hcst : cst = fun t => kcst (P.I.tup t) := eq_of_heq kerTie.2.2.2.2.2.2.2.1
  subst hcst
  have hLi : Li = fun t => kidx (P.I.tup t) := eq_of_heq kerTie.2.2.2.2.2.2.2.2.1
  subst hLi
  have hm2 : m2 = km2 := kerTie.2.2.2.2.2.2.2.2.2.1
  subst hm2
  have hGc : Gc = kglob := eq_of_heq kerTie.2.2.2.2.2.2.2.2.2.2.1
  subst hGc
  have hAm : Am = Formalism.L2.Ker.ambOf seam B χ cD := eq_of_heq kerTie.2.2.2.2.2.2.2.2.2.2.2.1
  subst hAm
  have hMem : Mem = D.what₂.Word := kerTie.2.2.2.2.2.2.2.2.2.2.2.2.1
  subst hMem
  have hwd : wd = kword := eq_of_heq kerTie.2.2.2.2.2.2.2.2.2.2.2.2.2
  subst hwd
  have hW' : W' = W := eq_of_heq hW
  subst hW'
  have hLv : Lv = Formalism.L2.Col.rPsymF (R := D.R) Ch' := lvTie
  subst hLv
  have hwu' : w = u := eq_of_heq hwu
  subst hwu'
  have hmuOne : ktup (P.I.tup P.A3.fam3.base3.μ0) = 1 := by rw [hmu0]; exact hKT.mu0
  have hev' := hev hmuOne
  dsimp only at hev'
  have key := hC0 D L hT Gi Gl Kc Y cX ex
    (⟨cc, cc_rec, cc_ok, δ, δ_ok, B, χ, χ_ok, idl, idl_ok, χ_rec, cD, fieldsLL D X e', seam, seam_ok, Pr, pr_ok, g_rec, Ch',
      sel, Sg, wd, T_rec, ktup, Q_rec, kcst, kidx, m2, Gc, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th,
      unf, ent, ent_lam, kf, kf_un, served⟩ : Formalism.L2.Ker.KerEntTied ex) W' Del h0 hX P.A3.fam3.base3
    (P.A3.side3 P.Ps P.ψs Pk.Zs) Xg P.I.tup hP b hY hK hF hE (ev Pk.Zs) w (Equiv.refl _) L.Nc lam0 c0 ce Ch Sw C1 H hmu0
    hKT hKS hCh hpos hev'
  dsimp only at key ha hlat ⊢
  obtain ⟨⟨ch, Tc, h1, X0, hX0, hn, hop, cb, hcb⟩, hXc⟩ := key
  exact ⟨ch, Tc, h1, X0, hX0, hn, hop, cb, hcb, hXc, ha, hlat⟩

end GlobalTheory.ColRows
end
