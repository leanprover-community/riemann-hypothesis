import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Statements
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ImportsMore
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ImportsTer
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeExact
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StandardInnerSingleNe
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StdCoordMapInjective
import GroundTheory.HeightsAndTheta.Heights.ArithDegree
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ExistsSmulMemOfSpanEqTop
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DegreeTopEqArithDegree
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalChange
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.LinearIndependentSumElimOfExact
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.ExistsSmulMemFamilyOfSpanEqTop
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ReMulOfPos

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open Matrix MeasureTheory

noncomputable section

def qf {ι : Type*} [Fintype ι] (Y : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := v ⬝ᵥ (Y *ᵥ v)

def intVec {ι : Type*} (v : ι → ℤ) : ι → ℝ := fun i => (v i : ℝ)

def firstMinSq {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) : ℝ :=
  ⨅ v : {v : ι → ℤ // v ≠ 0}, qf G (intVec v.1)

def siegelGram {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) :
    Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks Y⁻¹ (Y⁻¹ * X) (X * Y⁻¹) (Y + X * Y⁻¹ * X)

def S1.Statement : Prop :=
  ∀ (g : ℕ) (hg : 0 < g) (G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ),
    G ∈ symplecticGroup (Fin g) ℝ → G.PosDef →
    firstMinSq G ≤ 2 * g ∧
    ∃ M ∈ symplecticGroup (Fin g) ℤ,
      let G' := (M.map (Int.cast : ℤ → ℝ))ᵀ * G * M.map (Int.cast : ℤ → ℝ)
      G' (Sum.inl ⟨0, hg⟩) (Sum.inl ⟨0, hg⟩) = firstMinSq G ∧
      G'.toBlocks₁₁.det ≤ firstMinSq G * (2 * g) ^ (g - 1) ∧
      ∃ X Y : Matrix (Fin g) (Fin g) ℝ, X.IsSymm ∧ Y.PosDef ∧ G' = siegelGram X Y

def S2.Statement : Prop :=
  ∀ (g : ℕ) (hg : 0 < g) (Y : Matrix (Fin g) (Fin g) ℝ), Y.PosDef → ∀ v : Fin g → ℝ,
    v ⟨0, hg⟩ ^ 2 / Y⁻¹ ⟨0, hg⟩ ⟨0, hg⟩ ≤ qf Y v

def S3.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ), Y.PosDef → 0 < ρ →
    (∀ l : Fin g → ℤ, l ≠ 0 → ρ ^ 2 ≤ qf Y⁻¹ (intVec l)) → ∀ u : Fin g → ℝ,
      Summable (fun k : Fin g → ℤ => Real.exp (-(Real.pi / 2) * qf Y (intVec k + u))) ∧
      ∑' k : Fin g → ℤ, Real.exp (-(Real.pi / 2) * qf Y (intVec k + u)) ≤
        (C * g) ^ ((g : ℝ) / 2) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g

def tauOf {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g) (Fin g) ℂ :=
  X.map (fun x : ℝ => (x : ℂ)) + Complex.I • Y.map (fun x : ℝ => (x : ℂ))

def cvec {g : ℕ} (v : Fin g → ℝ) : Fin g → ℂ := fun i => (v i : ℂ)

def thetaChar {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (z : Fin g → ℂ) : ℂ :=
  ∑' k : Fin g → ℤ,
    Complex.exp (Real.pi * Complex.I *
        (cvec (intVec k + a) ⬝ᵥ (tauOf X Y *ᵥ cvec (intVec k + a))) +
      2 * Real.pi * Complex.I * (cvec (intVec k + a) ⬝ᵥ (z + cvec b)))

def thetaN {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (u₁ u₂ : Fin g → ℝ) : ℝ :=
  ‖thetaChar X Y a b (tauOf X Y *ᵥ cvec u₁ + cvec u₂)‖ * Real.exp (-Real.pi * qf Y u₁)

def thetaBeta {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) : ℝ :=
  ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 4 : ℝ))

def distInt (x : ℝ) : ℝ := |x - round x|

def IsHalfIntegral {g : ℕ} (a : Fin g → ℝ) : Prop := ∀ i, ∃ m : ℤ, a i = m / 2

def IsSiegelReducedCoordinates {g : ℕ} (hg : 0 < g) (X Y : Matrix (Fin g) (Fin g) ℝ) : Prop :=
  Y⁻¹ ⟨0, hg⟩ ⟨0, hg⟩ = firstMinSq (siegelGram X Y) ∧
    (Y⁻¹).det ≤ firstMinSq (siegelGram X Y) * (2 * g) ^ (g - 1)

def errE (C : ℝ) (g : ℕ) (ρ : ℝ) : ℝ :=
  g * Real.log (1 + 1 / ρ) + C * g * Real.log (2 * g)

def S4.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ) (hg : 0 < g) (X Y : Matrix (Fin g) (Fin g) ℝ),
    X.IsSymm → Y.PosDef → IsSiegelReducedCoordinates hg X Y → ∀ a b : Fin g → ℝ,
      IsHalfIntegral a → IsHalfIntegral b →
      (∫ u in Set.Icc (0 : (Fin g → ℝ) × (Fin g → ℝ)) 1, thetaN X Y a b u.1 u.2 ^ 2) =
          thetaBeta Y ^ 2 ∧
      ∀ u₁ u₂ : Fin g → ℝ,
        thetaN X Y a b u₁ u₂ ≤ thetaBeta Y * Real.exp
          (-(Real.pi / (2 * Y⁻¹ ⟨0, hg⟩ ⟨0, hg⟩)) * distInt (u₁ ⟨0, hg⟩ + a ⟨0, hg⟩) ^ 2 +
            errE C g (Real.sqrt (Y⁻¹ ⟨0, hg⟩ ⟨0, hg⟩)))

def mean {σ : Type*} [Fintype σ] (f : σ → ℝ) : ℝ := (∑ s, f s) / Fintype.card σ

def S5.Statement : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, 0 < C ∧
    ∀ (g : ℕ) (σ : Type) [Fintype σ] [Nonempty σ] (ρ : σ → ℝ) (Φ : ℝ),
      (∀ s, 0 < ρ s ∧ ρ s ≤ Real.sqrt (2 * g)) → 0 ≤ Φ →
      mean (fun s => Real.pi / 96 * (ρ s)⁻¹ ^ 2 - errE C₀ g (ρ s)) ≤ Φ →
      mean (fun s => (ρ s)⁻¹ ^ 2) ≤ C * (Φ + (g : ℝ) ^ 2 * Real.log (2 * g)) ∧
      mean (fun s => errE C₀ g (ρ s)) ≤ C * (Φ + (g : ℝ) ^ 2 * Real.log (2 * g)) ∧
      mean (fun s => max (Real.log (ρ s)⁻¹) 0) ≤
        1 / 2 * Real.log (1 + mean (fun s => (ρ s)⁻¹ ^ 2))

def firstMinimum {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ⨅ v : {v : L // v ≠ 0}, ‖(v.1 : EuclideanSpace ℝ (Fin n))‖

def shortVectorsIn {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {v | v ∈ L ∧ v ∈ V ∧ ‖v‖ ≤ r ∧ v ≠ 0}

def S8.Statement : Prop :=
  ∀ (n : ℕ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L],
    (firstMinimum L / Real.sqrt n) ^ n ≤ ZLattice.covolume L ∧
    ∀ (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (r : ℝ), firstMinimum L ≤ r →
      (shortVectorsIn L V r).Finite ∧
      ((shortVectorsIn L V r).ncard : ℝ) ≤ (3 * r / firstMinimum L) ^ Module.finrank ℝ V - 1

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

abbrev ProjFunField (K : Type) [Field K] (i : ℕ) : Type := FractionRing (MvPolynomial (Fin (i - 1)) K)

def projCoord (K : Type) [Field K] (i : ℕ) (j : Fin i) : ProjFunField K i :=
  if h : (j : ℕ) = 0 then 1
  else algebraMap (MvPolynomial (Fin (i - 1)) K) (ProjFunField K i) (X ⟨(j : ℕ) - 1, by omega⟩)

abbrev OKBlock (d i : ℕ) : Unit → Type := fun _ => Fin d × Fin i

def okPoint (K : Type) [Field K] [NumberField K] {d : ℕ} (i : ℕ) (ω : Module.Basis (Fin d) ℤ (𝓞 K)) :
    (Σ _ : Unit, Fin d × Fin i) → ProjFunField K i :=
  fun p => algebraMap K (ProjFunField K i) (ω p.2.1 : K) * projCoord K i p.2.2

def pointOver {K : Type} [Field K] [NumberField K] {d i : ℕ} (ω : Module.Basis (Fin d) ℤ (𝓞 K))
    (σ : K →+* ℂ) (w : Fin i → ℂ) : (Σ _ : Unit, Fin d × Fin i) → ℂ :=
  fun p => σ (ω p.2.1 : K) * w p.2.2

def latticeNorm {K : Type} [Field K] [NumberField K] {i : ℕ}
    (hm : GroundTheory.Heights₂.Heights.HermitianMetric K (Fin i → 𝓞 K)) (σ : K →+* ℂ) (w : Fin i → ℂ) : ℝ :=
  Real.sqrt ((hm.form σ).inner
    ((GroundTheory.Heights₂.Heights.standardCoord K σ (Fin i)).symm (WithLp.toLp 2 w))
    ((GroundTheory.Heights₂.Heights.standardCoord K σ (Fin i)).symm (WithLp.toLp 2 w))).re

def IsLatticeBundle {K : Type} [Field K] [NumberField K] {d i : ℕ}
    (ω : Module.Basis (Fin d) ℤ (𝓞 K)) (hm : GroundTheory.Heights₂.Heights.HermitianMetric K (Fin i → 𝓞 K))
    (A : HermLine (OKBlock d i)) : Prop :=
  A.a = 1 ∧ IsSmoothHerm A ∧ IsConjInvariantH A ∧
    ∀ (σ : K →+* ℂ) (w : Fin i → ℂ), w ≠ 0 → A.h (pointOver ω σ w) = latticeNorm hm σ w

def freeBundle {K : Type} [Field K] [NumberField K] {i : ℕ}
    (hm : GroundTheory.Heights₂.Heights.HermitianMetric K (Fin i → 𝓞 K)) :
    GroundTheory.Heights₂.Heights.HermitianBundle.{0} K :=
  ⟨Fin i → 𝓞 K, hm⟩

def S7.Statement : Prop :=
  SuccessiveMinimaLowerBound →
  ∀ (K : Type) [Field K] [NumberField K] (d i : ℕ) (ω : Module.Basis (Fin d) ℤ (𝓞 K))
    (hm : GroundTheory.Heights₂.Heights.HermitianMetric K (Fin i → 𝓞 K)) (A : HermLine (OKBlock d i))
    (ε : ℝ) (II : IntersectionSystem),
    1 ≤ i → 0 < ε → IsLatticeBundle ω hm A → IsIntersectionSystem II →
    IsArithVar (mCoordIdeal (okPoint K i ω)) i ∧ Birational (okPoint K i ω) ∧
    ∃ W : Ideal (MRing (OKBlock d i)), IsArithVar W 1 ∧ mCoordIdeal (okPoint K i ω) ≤ W ∧
      -II Unit (OKBlock d i) W 1 ![A] / degC W ≤
        -(freeBundle hm).slope ⊤ + 1 / 2 * Real.log i + ε

abbrev GrBlock (f N j : ℕ) : Fin f → Type := fun _ => {I : Finset (Fin N) // I.card = j}

abbrev GrFunField (f N j : ℕ) : Type := FractionRing (MvPolynomial (Fin f × Fin j × Fin (N - j)) ℚ)

def grMatrix (f N j : ℕ) (τ : Fin f) : Matrix (Fin j) (Fin N) (GrFunField f N j) :=
  fun a c => if h : (c : ℕ) < j then (if (c : ℕ) = a then 1 else 0)
    else algebraMap (MvPolynomial (Fin f × Fin j × Fin (N - j)) ℚ) (GrFunField f N j)
      (X ((τ, a, ⟨(c : ℕ) - j, by omega⟩) : Fin f × Fin j × Fin (N - j)))

def grPoint (f N j : ℕ) : (Σ τ : Fin f, GrBlock f N j τ) → GrFunField f N j :=
  fun p => (Matrix.of fun a b : Fin j => grMatrix f N j p.1 a (p.2.1.orderEmbOfFin p.2.2 b)).det

def grFS (f N j : ℕ) : HermLine (GrBlock f N j) := HermLine.sqMetric 1

def MirabolicColumnBlock.Statement : Prop :=
  SuccessiveMinimaUpperBound →
  ∀ (f N j : ℕ) (II : IntersectionSystem), 1 ≤ f → j ≤ N → IsIntersectionSystem II →
    IsArithVar (mCoordIdeal (grPoint f N j)) (f * j * (N - j) + 1) ∧
    II (Fin f) (GrBlock f N j) (mCoordIdeal (grPoint f N j)) (f * j * (N - j) + 1)
        (fun _ => grFS f N j) ≤
      ((f * j * (N - j) + 1 : ℕ) : ℝ) * ((f * j : ℕ) / 2 * Real.log (N + 1)) *
        geomDeg (mCoordIdeal (grPoint f N j)) (grFS f N j) (f * j * (N - j))

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open MvPolynomial

noncomputable section

abbrev RootPoly (f N : ℕ) : Type := MvPolynomial (Fin f × Fin N) ℚ

def alternant {R : Type*} [CommRing R] {m : ℕ} (e : Fin m → ℕ) (v : Fin m → R) : R :=
  (Matrix.of fun i j : Fin m => v i ^ e j).det

def staircase (m : ℕ) : Fin m → ℕ := fun j => m - 1 - (j : ℕ)

def blockRoots (f N : ℕ) (τ : Fin f) : Fin N → RootPoly f N := fun i => X (τ, i)

def antisymBlocks (f N : ℕ) (H : RootPoly f N) : RootPoly f N :=
  ∑ w : Fin f → Equiv.Perm (Fin N),
    (∏ τ, ((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℚ) • rename (fun p => (p.1, w p.1 p.2)) H

def divDiff (f N : ℕ) (H : RootPoly f N) : RootPoly f N := by
  classical
  exact if h : ∃ P, antisymBlocks f N H = (∏ τ, alternant (staircase N) (blockRoots f N τ)) * P
    then h.choose else 0

def flagInt (f N : ℕ) (H : RootPoly f N) : ℚ := constantCoeff (divDiff f N H)

def blockPsum (f N : ℕ) (k : ℕ) (τ : Fin f) : RootPoly f N := ∑ i : Fin N, X (τ, i) ^ k

inductive SmallCase
  | last
  | first

def smallRoots (f r a : ℕ) : SmallCase → Fin f → Fin r → RootPoly f (r + a)
  | .last, τ, i => X (τ, ⟨a + i, by omega⟩)
  | .first, τ, i => -X (τ, ⟨i, by omega⟩)

def otherRoots (f r a : ℕ) : SmallCase → Fin f → Fin a → RootPoly f (r + a)
  | .last, τ, i => X (τ, ⟨i, by omega⟩)
  | .first, τ, i => X (τ, ⟨r + i, by omega⟩)

def smallMu (f r a : ℕ) (c : SmallCase) : RootPoly f (r + a) :=
  ∑ τ, ∑ i, smallRoots f r a c τ i

def fibClass (f r a : ℕ) (c : SmallCase) : RootPoly f (r + a) :=
  ∏ τ, alternant (staircase r) (smallRoots f r a c τ) * alternant (staircase a) (otherRoots f r a c τ)

def restPoly (f r a : ℕ) (c : SmallCase) : RootPoly f (r + a) :=
  smallMu f r a c ^ (f * (r * a) + 1) * fibClass f r a c

def restJ (f r a : ℕ) (c : SmallCase) : ℚ :=
  flagInt f (r + a) (smallMu f r a c ^ (f * (r * a)) * fibClass f r a c)

def IsPsumDecomposition (f N : ℕ) (F : RootPoly f N) (Q : ℕ → Fin f → RootPoly f N) : Prop :=
  F = ∑ k ∈ Finset.Icc 1 N, ∑ τ, blockPsum f N k τ * Q k τ

def termT (f N : ℕ) (Q : ℕ → Fin f → RootPoly f N) (k : ℕ) (τ : Fin f) (G : RootPoly f N) : ℚ :=
  k * flagInt f N (G * Q k τ)

def restAtPrime (f r a : ℕ) (c : SmallCase) (Q : ℕ → Fin f → RootPoly f (r + a))
    (s : ℕ → ℕ → Fin f → Fin f) (e : ℕ → ℕ → Fin f → ℕ → ℚ) (p : ℕ) : ℝ :=
  Real.log p * ∑ τ, ∑ k ∈ Finset.Icc 2 (r + a), ∑' n' : ℕ,
    ((p : ℝ) ^ ((n' + 1) * k))⁻¹ *
      ((termT f (r + a) Q k τ
        (C (e p (n' + 1) τ k) * ∑ i, smallRoots f r a c (s p (n' + 1) τ) i ^ (k - 1)) : ℚ) : ℝ)

def S9.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (f r a : ℕ) (c : SmallCase) (B₀ : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ →
    (∃ Q, IsPsumDecomposition f (r + a) (restPoly f r a c) Q) ∧
    ∀ Q : ℕ → Fin f → RootPoly f (r + a), IsPsumDecomposition f (r + a) (restPoly f r a c) Q →
    ∀ (s : ℕ → ℕ → Fin f → Fin f) (e : ℕ → ℕ → Fin f → ℕ → ℚ),
      (∀ p n' τ k, e p n' τ k = 1 ∨ e p n' τ k = -1) → ∀ S : Set ℕ,
      Summable (fun p : {p : ℕ // p ∈ S ∧ p.Prime ∧ B₀ < p} => |restAtPrime f r a c Q s e p|) ∧
      |∑' p : {p : ℕ // p ∈ S ∧ p.Prime ∧ B₀ < p}, restAtPrime f r a c Q s e p| ≤
        C * r * ((f * (r * a) + 1 : ℕ) : ℝ) * |(restJ f r a c : ℝ)|

def inhQ : ℕ → Fin 1 → RootPoly 1 (1 + 1) :=
  fun k _ => if k = 1 then C (2⁻¹ : ℚ) * (X (0, 1) - X (0, 0)) else if k = 2 then C (2⁻¹ : ℚ) else 0

theorem S9.hypotheses_inhabited :
    4 * ((1 : ℕ) : ℝ) * ((1 + 1 : ℕ) : ℝ) ^ 2 ≤ 16 ∧
      IsPsumDecomposition 1 (1 + 1) (restPoly 1 1 1 .last) inhQ ∧
      ∀ (p n' : ℕ) (τ : Fin 1) (k : ℕ), (fun _ _ _ _ => (1 : ℚ)) p n' τ k = 1 ∨
        (fun _ _ _ _ => (1 : ℚ)) p n' τ k = -1 := by
  refine ⟨by norm_num, ?_, fun _ _ _ _ => Or.inl rfl⟩
  have hI : Finset.Icc 1 (1 + 1) = ({1, 2} : Finset ℕ) := by decide
  simp only [IsPsumDecomposition, restPoly, smallMu, fibClass, alternant, smallRoots,
    otherRoots, hI, inhQ, blockPsum, Matrix.det_unique, Finset.univ_unique, Finset.sum_singleton,
    Finset.prod_singleton]
  rw [Finset.sum_pair (by norm_num)]
  simp [staircase, Fin.sum_univ_succ]
  have h2 : (C (2⁻¹ : ℚ) : RootPoly 1 (1 + 1)) * 2 = 1 := by
    rw [show (2 : RootPoly 1 (1 + 1)) = C 2 from (map_ofNat C 2).symm, ← C_mul]; norm_num
  linear_combination (-X ((0 : Fin 1), (1 : Fin (1 + 1))) ^ 2) * h2

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights TensorProduct
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in

theorem mem_coordLine {n : ℕ} {a : Fin n → FractionalIdeal (𝓞 K)⁰ K} {x : Fin n}
    {w : idealLattice a} : w ∈ coordLine a x ↔ ∀ y, y ≠ x → (w : Fin n → K) y = 0 := by
  simp only [coordLine, satSub, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.restrictScalars_mem, Set.range_const, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, ht⟩ y hy
    rw [← ht]
    simp [hy]
  · intro h
    refine ⟨(w : Fin n → K) x, funext fun y => ?_⟩
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy, h y hy]

omit [NumberField K] in

theorem single_mem_idealLattice {n : ℕ} {a : Fin n → FractionalIdeal (𝓞 K)⁰ K} (v : idealLattice a)
    (x : Fin n) : (Pi.single x ((v : Fin n → K) x) : Fin n → K) ∈ idealLattice a := by
  have hv := v.2
  unfold idealLattice at hv ⊢
  rw [Submodule.mem_pi] at hv ⊢
  intro y _
  by_cases hy : y = x
  · subst hy; simpa using hv y (Set.mem_univ _)
  · simp [Pi.single_apply, hy]

theorem coordLine_isInternal {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    DirectSum.IsInternal (coordLine a) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro x
    rw [Submodule.disjoint_def]
    intro w hw hw'
    have hle : (⨆ j, ⨆ (_ : j ≠ x), coordLine a j) ≤
        LinearMap.ker ((LinearMap.proj (R := 𝓞 K) (φ := fun _ : Fin n => K) x) ∘ₗ
          (idealLattice a).subtype) :=
      iSup₂_le fun j hj v hv => by
        simp [mem_coordLine.mp hv x (Ne.symm hj)]
    have h0 : (w : Fin n → K) x = 0 := by simpa using hle hw'
    ext y
    by_cases hy : y = x
    · subst hy; simpa using h0
    · simpa using mem_coordLine.mp hw y hy
  · refine eq_top_iff.mpr fun w _ => ?_
    have hw : w = ∑ x, (⟨_, single_mem_idealLattice w x⟩ : idealLattice a) := by
      ext y
      simp [Submodule.coe_sum, Finset.sum_apply, Pi.single_apply]
    rw [hw]
    refine Submodule.sum_mem _ fun x _ => Submodule.mem_iSup_of_mem x (mem_coordLine.mpr ?_)
    intro y hy
    simp [Pi.single_apply, hy]

theorem coordLine_orthogonal {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (d : (K →+* ℂ) → Fin n → ℝ) (hd : ∀ σ x, 0 < d σ x) (hc : ∀ σ x, d (conjugate σ) x = d σ x) :
    IsOrthogonalFamily (latticeBundle a d hd hc) (coordLine a) := by
  intro σ x y hxy l hl l' hl'
  refine (matrixMetric_inner_one_tmul (idealLattice a) (diagMetric d) (diagMetric_posDef hd)
    (diagMetric_conj hc) σ l l').trans ?_
  simp only [diagMetric, mulVec_diagonal, dotProduct, embVec, Pi.star_apply]
  refine Finset.sum_eq_zero fun z _ => ?_
  by_cases hz : z = x
  · subst hz
    simp [mem_coordLine.mp hl' z hxy]
  · simp [mem_coordLine.mp hl z hz]

theorem S6.LatticeAsBundle.proof (hS : S6.MatrixSubDegree.Statement)
    (hE : S6.QuotExtension.Statement) (hQ : S6.QuotDegree.Statement) :
    S6.LatticeAsBundle.Statement := by
  intro K _ _ n a d ha hd hc
  have hspan := (LinesIdealLatticeFG.full K n a ha).2
  have hline : ∀ x : Fin n, LinearIndependent K (fun _ : Fin 1 => (Pi.single x 1 : Fin n → K)) :=
    fun x => linearIndependent_unique_iff.mpr (by simp)
  refine ⟨latticeBundle a d hd hc, coordLine a, coordLine_isInternal a, fun x => ?_,
    coordLine_orthogonal a d hd hc, fun x => ?_, ?_⟩
  · exact (hS K n (idealLattice a) (diagMetric d) (diagMetric_posDef hd) (diagMetric_conj hc)
      hspan 1 _ (hline x)).1
  · have h := (hS K n (idealLattice a) (diagMetric d) (diagMetric_posDef hd) (diagMetric_conj hc)
      hspan 1 _ (hline x)).2
    unfold HermitianBundle.normDegree normalise
    exact congrArg (· / (Module.finrank ℚ K : ℝ)) h
  · intro m k b c hli hmk
    obtain ⟨X, -, -⟩ := hE K n a d hd hc ha m k b c hli hmk
    obtain ⟨hspan'', hdeg⟩ := hQ K n a d ha hd m k b c hli hmk
    have hstd : (fun j : Fin k => (Pi.single j 1 : Fin k → K)) = ⇑(Pi.basisFun K (Fin k)) :=
      funext fun j => (Pi.basisFun_apply K (Fin k) j).symm
    have htop : satSub (quotLattice a b c hli hmk) (fun j : Fin k => (Pi.single j 1 : Fin k → K)) =
        ⊤ := by
      refine eq_top_iff.mpr fun w _ => ?_
      simp only [satSub, Submodule.mem_comap, Submodule.restrictScalars_mem, hstd,
        (Pi.basisFun K (Fin k)).span_eq, Submodule.mem_top]
    obtain ⟨hr, hdg⟩ := hS K k (quotLattice a b c hli hmk) (schurMetric d b c)
      (schurMetric_posDef hd hli) (schurMetric_conj hc b c) hspan'' k _
      (hstd ▸ (Pi.basisFun K (Fin k)).linearIndependent)
    rw [htop] at hr hdg
    refine ⟨subBundle a d hd hc b, quotBundle a d hd hc b c hli hmk, ⟨X⟩, hr, ?_⟩
    unfold HermitianBundle.normDegree normalise
    exact congrArg (· / (Module.finrank ℚ K : ℝ)) (hdg.trans hdeg)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

noncomputable section

def S6.BundleCoordinates.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (X : Type) [Fintype X]
    [DecidableEq X] (L : X → Submodule (𝓞 K) E.carrier),
    DirectSum.IsInternal L → (∀ x, E.rank (L x) = 1) → IsOrthogonalFamily E L →
    ∀ (E' E'' : HermitianBundle.{0} K), HermitianExtension E' E E'' →
    ∃ (n : ℕ) (e : Fin n ≃ X) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (d : (K →+* ℂ) → Fin n → ℝ),
      (∀ i, a i ≠ 0) ∧ (∀ σ i, 0 < d σ i) ∧ (∀ σ i, d (conjugate σ) i = d σ i) ∧
      (∀ i, GroundTheory.Heights₂.Heights.normalise K
        (GroundTheory.Heights₂.Heights.subDegree (GroundTheory.Heights₂.Heights.idealLattice a)
          (GroundTheory.Heights₂.Heights.diagMetric d) (fun _ : Fin 1 => (Pi.single i 1 : Fin n → K))) =
        E.normDegree (L (e i))) ∧
      ∃ (m k : ℕ) (b : Fin m → Fin n → K) (c : Fin k → Fin n → K),
        LinearIndependent K (Sum.elim b c) ∧ m + k = n ∧ k = E''.rank ⊤ ∧
        GroundTheory.Heights₂.Heights.normalise K
          (GroundTheory.Heights₂.Heights.quotDegree (GroundTheory.Heights₂.Heights.idealLattice a)
            (GroundTheory.Heights₂.Heights.diagMetric d) b c) = E''.normDegree ⊤

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding GroundTheory.Heights₂.Heights

noncomputable section

theorem range_incl_saturated {K : Type*} [Field K] [NumberField K]
    {E' E E'' : HermitianBundle K} (Y : HermitianExtension E' E E'') (t : 𝓞 K) (x : E.carrier)
    (ht : t ≠ 0) (hx : t • x ∈ LinearMap.range Y.incl) : x ∈ LinearMap.range Y.incl := by
  rw [← Y.exact.linearMap_ker_eq, LinearMap.mem_ker] at hx ⊢
  rw [map_smul] at hx
  exact (smul_eq_zero.mp hx).resolve_left ht

theorem S6.BundleCoordinates.proof (hA : S6.LineCoordinates.Statement)
    (hB : S6.CoordinateDegree.Statement) (hC : S6.QuotientDegreeSplit.Statement)
    (hD : S6.ExtensionDegree.Statement) (hE : S6.SaturatedSpan.Statement) :
    S6.BundleCoordinates.Statement := by
  intro K _ _ E X _ _ L hI hr ho E' E'' Y
  obtain ⟨n, e, a, d, ψ, ha, hd, hc, hψ, hrange, hfin, hline, hmet⟩ := hA K E X L hI hr ho
  obtain ⟨hFG, hspanA⟩ := LinesIdealLatticeFG.full K n a ha
  have hspan : Submodule.span K (LinearMap.range ψ : Set (Fin n → K)) = ⊤ := by
    rw [hrange]; exact hspanA
  have hdeg := hB K E n (diagMetric d) ψ hψ hspan hmet
  refine ⟨n, e, a, d, ha, hd, hc, fun i => ?_, ?_⟩
  ·
    have hu : LinearIndependent K (fun _ : Fin 1 => (Pi.single i 1 : Fin n → K)) :=
      linearIndependent_unique_iff.mpr (by simp)
    have h1 := hdeg (L (e i)) (Fin 1) _ hu (by rw [hline i, hrange, Set.range_const])
    rw [HermitianBundle.normDegree, h1, hrange]
    rfl
  ·
    set G := LinearMap.range Y.incl
    obtain ⟨b, hb, hbmap⟩ := hE K E.carrier n ψ hψ G (range_incl_saturated Y)
    have hGr : Module.finrank (𝓞 K) G = Module.finrank (𝓞 K) E'.carrier :=
      LinearMap.finrank_range_of_inj Y.incl_injective
    have hmk : Module.finrank (𝓞 K) G + E''.rank ⊤ = n := by
      rw [hGr, HermitianBundle.rank, finrank_top, ← hfin, Y.finrank_eq]
    obtain ⟨τ, -, hli⟩ := LinesExtendBasis.full K n _ _ b hb hmk
    refine ⟨_, _, b, fun j => Pi.single (τ j) 1, hli, hmk, rfl, ?_⟩
    have htop : Submodule.span K
        (Set.range (Sum.elim b fun j => (Pi.single (τ j) 1 : Fin n → K))) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by
        rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Module.finrank_fin_fun, hmk])
    have hE1 := hdeg ⊤ _ (Sum.elim b fun j => (Pi.single (τ j) 1 : Fin n → K)) hli (by
      rw [Submodule.map_top, htop, Submodule.restrictScalars_top, inf_top_eq])
    have hG1 := hdeg G _ b hb hbmap
    rw [hC K n (idealLattice a) (diagMetric d) hFG hspanA _ _ b _ hli hmk,
      HermitianBundle.normDegree, hD K E' E E'' Y, hE1, hG1, hrange]
    rfl

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

noncomputable section

section Coefficient

variable {K : Type*} [Field K] [NumberField K] {E : HermitianBundle K}

theorem exists_smul_eq_smul_of_finrank_one {N : Submodule (𝓞 K) E.carrier}
    (hN : Module.finrank (𝓞 K) N = 1) {l : E.carrier} (hl : l ∈ N) (hl0 : l ≠ 0)
    {w : E.carrier} (hw : w ∈ N) : ∃ t s : 𝓞 K, t ≠ 0 ∧ t • w = s • l := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hli : LinearIndependent (𝓞 K) ![(⟨w, hw⟩ : N), ⟨l, hl⟩] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h : s • w + t • l = 0 := congrArg Subtype.val hst
    by_cases hs : s = 0
    · subst hs
      rw [zero_smul, zero_add] at h
      exact ⟨rfl, (smul_eq_zero.mp h).resolve_right hl0⟩
    · exact absurd (by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h) (hcon s (-t) hs)
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, hN] at this
  omega

theorem lineCoef_ratio_unique {l w : E.carrier} (hl0 : l ≠ 0) {t s t' s' : 𝓞 K} (ht : t ≠ 0) (ht' : t' ≠ 0)
    (h : t • w = s • l) (h' : t' • w = s' • l) : (s : K) / t = s' / t' := by
  have key : (t' * s - t * s') • l = 0 := by
    rw [sub_smul, mul_smul, mul_smul, ← h, ← h', smul_comm t' t, sub_self]
  have key' : t' * s = t * s' := sub_eq_zero.mp ((smul_eq_zero.mp key).resolve_right hl0)
  have h1 : (t : K) ≠ 0 := by exact_mod_cast ht
  have h2 : (t' : K) ≠ 0 := by exact_mod_cast ht'
  have h3 := congrArg (fun x : 𝓞 K => (x : K)) key'
  push_cast at h3
  rw [div_eq_div_iff h1 h2]
  linear_combination h3

variable {N : Submodule (𝓞 K) E.carrier} (hN : Module.finrank (𝓞 K) N = 1) {l : E.carrier}
  (hl : l ∈ N) (hl0 : l ≠ 0)

def lineCoefFun (w : N) : K :=
  ((exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2).choose_spec.choose : K) /
    ((exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2).choose : K)

theorem lineCoefFun_eq (w : N) {t s : 𝓞 K} (ht : t ≠ 0) (h : t • (w : E.carrier) = s • l) :
    lineCoefFun hN hl hl0 w = (s : K) / t :=
  lineCoef_ratio_unique hl0 (exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2).choose_spec.choose_spec.1 ht
    (exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2).choose_spec.choose_spec.2 h

def lineCoef : N →ₗ[𝓞 K] K where
  toFun := lineCoefFun hN hl hl0
  map_add' w w' := by
    obtain ⟨t, s, ht, h⟩ := exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2
    obtain ⟨t', s', ht', h'⟩ := exists_smul_eq_smul_of_finrank_one hN hl hl0 w'.2
    have h'' : (t * t') • ((w + w' : N) : E.carrier) = (t' * s + t * s') • l := by
      rw [Submodule.coe_add, smul_add, mul_smul, mul_smul, h', smul_comm t t' (w : E.carrier), h,
        ← mul_smul, ← mul_smul, ← add_smul]
    rw [lineCoefFun_eq hN hl hl0 w ht h, lineCoefFun_eq hN hl hl0 w' ht' h',
      lineCoefFun_eq hN hl hl0 (w + w') (mul_ne_zero ht ht') h'']
    have h1 : (t : K) ≠ 0 := by exact_mod_cast ht
    have h2 : (t' : K) ≠ 0 := by exact_mod_cast ht'
    push_cast
    field_simp
  map_smul' c w := by
    obtain ⟨t, s, ht, h⟩ := exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2
    have h' : t • ((c • w : N) : E.carrier) = (c * s) • l := by
      rw [Submodule.coe_smul, smul_comm, h, mul_smul]
    rw [lineCoefFun_eq hN hl hl0 w ht h, lineCoefFun_eq hN hl hl0 (c • w) ht h', RingHom.id_apply,
      Algebra.smul_def]
    push_cast
    rw [mul_div_assoc]

theorem lineCoef_eq (w : N) {t s : 𝓞 K} (ht : t ≠ 0) (h : t • (w : E.carrier) = s • l) :
    lineCoef hN hl hl0 w = (s : K) / t :=
  lineCoefFun_eq hN hl hl0 w ht h

theorem lineCoef_self : lineCoef hN hl hl0 ⟨l, hl⟩ = 1 := by
  rw [lineCoef_eq hN hl hl0 ⟨l, hl⟩ (t := 1) (s := 1) one_ne_zero rfl]
  simp

theorem lineCoef_eq_zero {w : N} (hw : lineCoef hN hl hl0 w = 0) : (w : E.carrier) = 0 := by
  obtain ⟨t, s, ht, h⟩ := exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2
  rw [lineCoef_eq hN hl hl0 w ht h, div_eq_zero_iff] at hw
  have hs : s = 0 := by
    rcases hw with hw | hw
    · exact_mod_cast hw
    · exact absurd hw (by exact_mod_cast ht)
  rw [hs, zero_smul] at h
  exact (smul_eq_zero.mp h).resolve_left ht

theorem fibreVec_lineCoef (σ : K →+* ℂ) (w : N) :
    fibreVec E.metric σ (w : E.carrier) = σ (lineCoef hN hl hl0 w) • fibreVec E.metric σ l := by
  obtain ⟨t, s, ht, h⟩ := exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2
  have hst : σ (t : K) ≠ 0 := by rw [map_ne_zero]; exact_mod_cast ht
  have h1 := congrArg (fibreVec E.metric σ) h
  rw [fibreVec_smul, fibreVec_smul] at h1
  rw [lineCoef_eq hN hl hl0 w ht h, map_div₀, div_eq_inv_mul, mul_smul, ← h1, smul_smul,
    inv_mul_cancel₀ hst, one_smul]

end Coefficient

theorem fibreVec_finset_sum {K : Type*} [Field K] [NumberField K] {E : HermitianBundle K} (σ : K →+* ℂ)
    {ι : Type*} (S : Finset ι) (f : ι → E.carrier) :
    fibreVec E.metric σ (∑ i ∈ S, f i) = ∑ i ∈ S, fibreVec E.metric σ (f i) := by
  simp only [fibreVec, tmul_sum, map_sum]

theorem S6.LineCoordinates.proof : S6.LineCoordinates.Statement := by
  intro K _ _ E X _ _ L hI hr ho
  set n := Fintype.card X
  let e : Fin n ≃ X := (Fintype.equivFin X).symm
  have hne : ∀ x, ∃ l ∈ L x, l ≠ 0 := by
    intro x
    have hb : L x ≠ ⊥ := by
      intro h
      have h1 := hr x
      rw [h] at h1
      simp [HermitianBundle.rank] at h1
    exact (Submodule.ne_bot_iff _).mp hb
  choose l hl hl0 using hne
  let α : ∀ x, L x →ₗ[𝓞 K] K := fun x => lineCoef (hr x) (hl x) (hl0 x)
  let Φ := LinearEquiv.ofBijective (DirectSum.coeLinearMap L) hI
  let comp : ∀ x, E.carrier →ₗ[𝓞 K] L x := fun x =>
    (DirectSum.component (𝓞 K) X (fun x => L x) x).comp Φ.symm.toLinearMap
  have hcomp_same : ∀ x (w : E.carrier) (hw : w ∈ L x), comp x w = ⟨w, hw⟩ := fun x w hw =>
    hI.ofBijective_coeLinearMap_of_mem hw
  have hcomp_ne : ∀ x y (w : E.carrier), w ∈ L x → x ≠ y → comp y w = 0 := fun x y w hw hxy =>
    hI.ofBijective_coeLinearMap_of_mem_ne hxy hw
  have hsum : ∀ v : E.carrier, ∑ x, (comp x v : E.carrier) = v := by
    intro v
    conv_rhs => rw [← Φ.apply_symm_apply v, ← DirectSum.sum_univ_of (Φ.symm v)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    show _ = DirectSum.coeLinearMap L (DirectSum.of (fun i => L i) x (Φ.symm v x))
    rw [DirectSum.coeLinearMap_of]
    rfl
  let ψ : E.carrier →ₗ[𝓞 K] (Fin n → K) := LinearMap.pi fun i => (α (e i)).comp (comp (e i))
  have hψ_apply : ∀ v i, ψ v i = α (e i) (comp (e i) v) := fun _ _ => rfl
  have hψ_line : ∀ i (w : E.carrier) (hw : w ∈ L (e i)),
      ψ w = Pi.single i (α (e i) ⟨w, hw⟩) := by
    intro i w hw
    funext j
    rw [hψ_apply]
    by_cases hj : j = i
    · subst hj
      rw [hcomp_same _ w hw, Pi.single_eq_same]
    · rw [hcomp_ne _ _ w hw (e.injective.ne (Ne.symm hj)), map_zero, Pi.single_eq_of_ne hj]

  have hfrac : ∀ i, IsFractional (𝓞 K)⁰ (LinearMap.range (α (e i))) := fun i =>
    FractionalIdeal.isFractional_of_fg (by
      rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _)
  let a : Fin n → FractionalIdeal (𝓞 K)⁰ K := fun i => ⟨LinearMap.range (α (e i)), hfrac i⟩
  have ha : ∀ i, a i ≠ 0 := by
    intro i h
    have h1 : (1 : K) ∈ (a i : Submodule (𝓞 K) K) :=
      LinearMap.mem_range.mpr ⟨⟨l (e i), hl (e i)⟩, lineCoef_self _ _ _⟩
    rw [h, FractionalIdeal.coe_zero, Submodule.mem_bot] at h1
    exact one_ne_zero h1

  have hψl : ∀ i, ψ (l (e i)) = Pi.single i 1 := fun i => by
    rw [hψ_line i _ (hl (e i))]
    exact congrArg (Pi.single i) (lineCoef_self _ _ _)
  have hlin : LinearIndependent (𝓞 K) (fun i => l (e i)) := by
    apply LinearIndependent.of_comp ψ
    have h1 : (ψ ∘ fun i => l (e i)) = fun i => Pi.basisFun K (Fin n) i := by
      funext i
      simp only [Function.comp_apply, hψl, Pi.basisFun_apply]
    rw [h1, LinearIndependent.iff_fractionRing (𝓞 K) K]
    exact (Pi.basisFun K (Fin n)).linearIndependent
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hc : ∀ i, comp (e i) v = 0 := by
      intro i
      have h := congrFun hv i
      rw [hψ_apply, Pi.zero_apply] at h
      exact Subtype.ext (lineCoef_eq_zero _ _ _ h)
    rw [← hsum v]
    refine Finset.sum_eq_zero fun x _ => ?_
    obtain ⟨i, rfl⟩ := e.surjective x
    rw [hc i, Submodule.coe_zero]
  have hrange : LinearMap.range ψ = idealLattice a := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      rw [idealLattice, Submodule.mem_pi]
      intro i _
      exact LinearMap.mem_range.mpr ⟨comp (e i) v, rfl⟩
    · intro f hf
      rw [idealLattice, Submodule.mem_pi] at hf
      have h1 : ∀ i, ∃ w : L (e i), α (e i) w = f i := fun i =>
        LinearMap.mem_range.mp (hf i (Set.mem_univ i))
      choose w hw using h1
      refine ⟨∑ i, (w i : E.carrier), ?_⟩
      have h2 : ∀ i, ψ (w i) = Pi.single i (f i) := fun i => by
        rw [hψ_line i _ (w i).2, ← hw i]
      rw [map_sum]
      simp only [h2]
      exact Finset.univ_sum_single f
  have hfin : Module.finrank (𝓞 K) E.carrier = n := by
    apply le_antisymm
    · obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 K) (M := E.carrier) le_rfl
      have h1 : LinearIndependent K (ψ ∘ f) := (LinearIndependent.iff_fractionRing (𝓞 K) K).mp
        (hf.map' ψ (LinearMap.ker_eq_bot.mpr hinj))
      simpa using h1.fintype_card_le_finrank
    · simpa using hlin.fintype_card_le_finrank
  have hlines : ∀ i, (L (e i)).map ψ = idealLattice a ⊓
      (Submodule.span K {(Pi.single i 1 : Fin n → K)}).restrictScalars (𝓞 K) := by
    intro i
    ext f
    simp only [Submodule.mem_map, Submodule.mem_inf, Submodule.restrictScalars_mem,
      Submodule.mem_span_singleton]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨hrange ▸ LinearMap.mem_range_self ψ w, α (e i) ⟨w, hw⟩, ?_⟩
      rw [hψ_line i w hw]
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_eq_of_ne hj]
    · rintro ⟨hf1, c, rfl⟩
      have hmem : (c • Pi.single i 1 : Fin n → K) i ∈ (a i : Submodule (𝓞 K) K) := by
        rw [idealLattice, Submodule.mem_pi] at hf1
        exact hf1 i (Set.mem_univ _)
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hmem
      refine ⟨w, w.2, ?_⟩
      rw [hψ_line i w w.2]
      rw [show α (e i) ⟨(w : E.carrier), w.2⟩ = α (e i) w from rfl, hw]
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_eq_of_ne hj]

  have hinnerF : ∀ σ (v w : E.carrier), inner ℂ (fibreVec E.metric σ v) (fibreVec E.metric σ w) =
      (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] w) :=
    fun _ _ _ => rfl
  let d : (K →+* ℂ) → Fin n → ℝ := fun σ i =>
    (inner ℂ (fibreVec E.metric σ (l (e i))) (fibreVec E.metric σ (l (e i)))).re
  have hF0 : ∀ σ i, fibreVec E.metric σ (l (e i)) ≠ 0 := fun σ i =>
    (linearIndependent_fibreVec E.metric σ hlin).ne_zero i
  have hd : ∀ σ i, 0 < d σ i := fun σ i => by
    have h := (re_inner_self_pos (𝕜 := ℂ)).mpr (hF0 σ i)
    rw [RCLike.re_to_complex] at h
    exact h
  have hc : ∀ σ i, d (conjugate σ) i = d σ i := fun σ i => by
    simp only [d, hinnerF]
    have h := E.metric.form_conj σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] l (e i))
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] l (e i))
    rw [conjMap_tmul, map_one] at h
    rw [h, Complex.conj_re]
  have hdi : ∀ σ i, inner ℂ (fibreVec E.metric σ (l (e i))) (fibreVec E.metric σ (l (e i))) =
      ((d σ i : ℝ) : ℂ) := fun σ i => by
    apply Complex.ext
    · simp [d]
    · simp only [Complex.ofReal_im, hinnerF]
      exact core_inner_self_im _ _

  have hexp : ∀ σ (v : E.carrier),
      fibreVec E.metric σ v = ∑ i, σ (ψ v i) • fibreVec E.metric σ (l (e i)) := by
    intro σ v
    conv_lhs => rw [← hsum v]
    rw [fibreVec_finset_sum, ← e.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact fibreVec_lineCoef (hr (e i)) (hl (e i)) (hl0 (e i)) σ (comp (e i) v)
  have hmet : ∀ (σ : K →+* ℂ) (v w : E.carrier),
      (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] w) =
        star (embVec σ (ψ v)) ⬝ᵥ (diagMetric d σ *ᵥ embVec σ (ψ w)) := by
    intro σ v w
    rw [← hinnerF, hexp σ v, hexp σ w, sum_inner]
    simp only [inner_sum, inner_smul_left, inner_smul_right]
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [hdi]
      simp only [diagMetric, mulVec_diagonal, embVec, Pi.star_apply, starRingEnd_apply]
      ring
    · intro j _ hji
      rw [hinnerF, ho σ (e i) (e j) (e.injective.ne (Ne.symm hji)) _ (hl _) _ (hl _), mul_zero,
        mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  exact ⟨n, e, a, d, ψ, ha, hd, hc, hinj, hrange, hfin, hlines, hmet⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

noncomputable section

namespace QuotientDegreeSplitAlt

theorem relIndex_split_of_le {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (π : G →+ G')
    {A C : AddSubgroup G} (hCA : C ≤ A) :
    C.relIndex A = C.relIndex (A ⊓ π.ker) * (C.map π).relIndex (A.map π) := by
  have h1 : (C.map π).relIndex (A.map π) = (C ⊔ π.ker).relIndex A := by
    rw [← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq]
  have hmod : (A ⊓ π.ker) ⊔ C = (C ⊔ π.ker) ⊓ A := by
    ext x
    simp only [AddSubgroup.mem_sup, AddSubgroup.mem_inf]
    constructor
    · rintro ⟨y, ⟨hyA, hyW⟩, z, hz, rfl⟩
      exact ⟨⟨z, hz, y, hyW, add_comm z y⟩, add_mem hyA (hCA hz)⟩
    · rintro ⟨⟨y, hy, z, hz, rfl⟩, hA⟩
      refine ⟨z, ⟨?_, hz⟩, y, hy, add_comm z y⟩
      have hz' : z = (y + z) - y := by abel
      rw [hz']
      exact sub_mem hA (hCA hy)
  have h2 : C.relIndex ((C ⊔ π.ker) ⊓ A) = C.relIndex (A ⊓ π.ker) := by
    rw [← hmod, AddSubgroup.relIndex_sup_right]
  rw [h1, ← h2, AddSubgroup.relIndex_inf_mul_relIndex, inf_of_le_left le_sup_left]

theorem genIndex_split {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (π : G →+ G')
    (A C : AddSubgroup G) (hpos : 0 < genIndex A C) :
    genIndex A C = genIndex (A ⊓ π.ker) (C ⊓ π.ker) * genIndex (A.map π) (C.map π) := by
  have hDA : (A ⊓ C).map π ≤ A.map π := AddSubgroup.map_mono inf_le_left
  have hDC : (A ⊓ C).map π ≤ C.map π := AddSubgroup.map_mono inf_le_right
  have hA : C.relIndex A = (A ⊓ C).relIndex (A ⊓ π.ker) * (((A ⊓ C).map π).relIndex
      (A.map π ⊓ C.map π) * (C.map π).relIndex (A.map π)) := by
    rw [← AddSubgroup.inf_relIndex_left A C, relIndex_split_of_le π (inf_le_left : A ⊓ C ≤ A),
      inf_comm (A.map π), AddSubgroup.relIndex_inf_mul_relIndex, inf_of_le_left hDC]
  have hC : A.relIndex C = (A ⊓ C).relIndex (C ⊓ π.ker) * (((A ⊓ C).map π).relIndex
      (A.map π ⊓ C.map π) * (A.map π).relIndex (C.map π)) := by
    rw [← AddSubgroup.inf_relIndex_right A C, relIndex_split_of_le π (inf_le_right : A ⊓ C ≤ C),
      AddSubgroup.relIndex_inf_mul_relIndex, inf_of_le_left hDA]
  have hW1 : (C ⊓ π.ker).relIndex (A ⊓ π.ker) = (A ⊓ C).relIndex (A ⊓ π.ker) := by
    rw [← AddSubgroup.inf_relIndex_right (C ⊓ π.ker), ← AddSubgroup.inf_relIndex_right (A ⊓ C)]
    congr 1
    ext x
    simp only [AddSubgroup.mem_inf]
    tauto
  have hW2 : (A ⊓ π.ker).relIndex (C ⊓ π.ker) = (A ⊓ C).relIndex (C ⊓ π.ker) := by
    rw [← AddSubgroup.inf_relIndex_right (A ⊓ π.ker), ← AddSubgroup.inf_relIndex_right (A ⊓ C)]
    congr 1
    ext x
    simp only [AddSubgroup.mem_inf]
    tauto
  have he : ((((A ⊓ C).map π).relIndex (A.map π ⊓ C.map π) : ℕ) : ℝ) ≠ 0 := by
    intro h0
    have hz : genIndex A C = 0 := by
      unfold genIndex
      rw [hA]
      push_cast
      rw [h0]
      simp
    linarith
  unfold genIndex
  rw [hA, hC, hW1, hW2]
  push_cast
  rw [div_mul_div_comm, mul_left_comm (((A ⊓ C).relIndex (A ⊓ π.ker) : ℕ) : ℝ),
    mul_left_comm (((A ⊓ C).relIndex (C ⊓ π.ker) : ℕ) : ℝ), mul_div_mul_left _ _ he]

end QuotientDegreeSplitAlt

open QuotientDegreeSplitAlt in

theorem S6.QuotientDegreeSplit.proof : S6.QuotientDegreeSplit.Statement := by
  intro K _ _ n Λ H hFG hspan m k b c hli hmk
  have hcard : Fintype.card (Fin m ⊕ Fin k) = Module.finrank K (Fin n → K) := by
    simp [hmk]
  set B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K) :=
    basisOfLinearIndependentOfCardEqFinrank' (Sum.elim b c) hli hcard with hBdef
  have hB : ⇑B = Sum.elim b c := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have hBl : (fun i => B (Sum.inl i)) = b := by
    funext i; simp [hB]
  set W : Submodule (𝓞 K) (Fin n → K) :=
    (Submodule.span K (Set.range b)).restrictScalars (𝓞 K) with hWdef
  set π' : (Fin n → K) →ₗ[𝓞 K] (Fin k → K) := (coordProj B).restrictScalars (𝓞 K) with hπ'
  have hkerK : ∀ v, coordProj B v = 0 ↔ v ∈ Submodule.span K (Set.range b) := by
    intro v
    rw [← LinearMap.mem_ker, KLinesQuotIndex.ker_coordProj, hBl]
  have hb0 : ∀ i, coordProj B (b i) = 0 := fun i =>
    (hkerK _).mpr (Submodule.subset_span ⟨i, rfl⟩)
  have hc1 : ∀ j, coordProj B (c j) = Pi.single j 1 := by
    intro j
    have hcj : c j = B (Sum.inr j) := by simp [hB]
    rw [hcj]
    funext j'
    simp [coordProj, Pi.single_apply, Finsupp.single_apply]
    by_cases h : j = j'
    · subst h; simp
    · simp [h, Ne.symm h]

  set O : Submodule (𝓞 K) (Fin n → K) := Submodule.span (𝓞 K) (Set.range (Sum.elim b c)) with hOdef
  have htop : Submodule.span K (Set.range (Sum.elim b c)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' hcard
  have hOspan : Submodule.span K (O : Set (Fin n → K)) = ⊤ := by
    rw [hOdef, Submodule.span_span_of_tower, htop]
  have hΛlat : Submodule.IsLattice ℚ (Λ.restrictScalars ℤ) :=
    LinesIsLattice.full K (Fin n) Λ hFG.restrictScalars hspan
  have hOlat : Submodule.IsLattice ℚ (O.restrictScalars ℤ) :=
    LinesIsLattice.full K (Fin n) O (Submodule.fg_span (Set.finite_range _)).restrictScalars hOspan
  have hpos : 0 < genIndex Λ.toAddSubgroup O.toAddSubgroup :=
    (LinesGenIndexTrans.full (Fin n → K) (Λ.restrictScalars ℤ) (O.restrictScalars ℤ)
      (O.restrictScalars ℤ) hΛlat hOlat hOlat).1

  have hker : (π' : (Fin n → K) →+ (Fin k → K)).ker = W.toAddSubgroup := by
    ext v
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, hWdef, Submodule.restrictScalars_mem,
      ← hkerK]
    rfl

  have hOW : O ⊓ W = Submodule.span (𝓞 K) (Set.range b) := by
    apply le_antisymm
    · rintro x ⟨hxO, hxW⟩
      obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hxO
      have h0 : π' (∑ i, r i • Sum.elim b c i) = 0 := (hkerK _).mpr hxW
      rw [Fintype.sum_sum_type] at h0 ⊢
      simp only [Sum.elim_inl, Sum.elim_inr] at h0 ⊢
      have hs : ∀ j, r (Sum.inr j) = 0 := by
        intro j
        have h1 := congrFun h0 j
        simp only [map_add, map_sum, map_smul, hπ', LinearMap.restrictScalars_apply, hb0, hc1,
          smul_zero, Finset.sum_const_zero, zero_add, Finset.sum_apply, Pi.smul_apply,
          Pi.single_apply, smul_ite, Finset.sum_ite_eq, Finset.mem_univ, if_true,
          Pi.zero_apply] at h1
        exact (smul_eq_zero.mp h1).resolve_right one_ne_zero
      simp only [hs, zero_smul, Finset.sum_const_zero, add_zero]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · refine le_inf (Submodule.span_mono ?_) (Submodule.span_le_restrictScalars (𝓞 K) K _)
      rintro _ ⟨i, rfl⟩
      exact ⟨Sum.inl i, rfl⟩

  have hOmap : O.map π' = Submodule.span (𝓞 K) (Set.range (coordProj B ∘ c)) := by
    have hcomp : ⇑π' ∘ Sum.elim b c = Sum.elim (fun _ => 0) (coordProj B ∘ c) := by
      funext x
      rcases x with i | j
      · exact hb0 i
      · rfl
    rw [hOdef, Submodule.map_span, ← Set.range_comp, hcomp, Set.Sum.elim_range,
      Submodule.span_union]
    have hbot : Submodule.span (𝓞 K) (Set.range (fun _ : Fin m => (0 : Fin k → K))) = ⊥ :=
      Submodule.span_eq_bot.mpr (by rintro _ ⟨i, rfl⟩; rfl)
    rw [hbot, bot_sup_eq]

  have hsplit := genIndex_split (π' : (Fin n → K) →+ (Fin k → K)) Λ.toAddSubgroup O.toAddSubgroup hpos
  rw [hker, ← Submodule.map_toAddSubgroup, ← Submodule.map_toAddSubgroup, hOmap] at hsplit
  have hinf1 : Λ.toAddSubgroup ⊓ W.toAddSubgroup = (Λ ⊓ W).toAddSubgroup := rfl
  have hinf2 : O.toAddSubgroup ⊓ W.toAddSubgroup = (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup := by
    rw [← hOW]; rfl
  rw [hinf1, hinf2] at hsplit
  have hq := LinesQuotIndex.full K n m k B Λ c
  rw [hBl] at hq

  set x := genIndex (Λ ⊓ W).toAddSubgroup (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup with hx
  set y := genIndex (Λ.map π').toAddSubgroup
    (Submodule.span (𝓞 K) (Set.range (coordProj B ∘ c))).toAddSubgroup with hy
  have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hxy : 0 < x * y := hsplit ▸ hpos
  have hxne : x ≠ 0 := by rintro h; rw [h, zero_mul] at hxy; exact lt_irrefl _ hxy
  have hyne : y ≠ 0 := by rintro h; rw [h, mul_zero] at hxy; exact lt_irrefl _ hxy
  unfold quotDegree subDegree
  rw [htop, Submodule.restrictScalars_top, inf_top_eq, hq, hsplit, Real.log_mul hxne hyne,
    Finset.sum_sub_distrib]
  ring

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField TensorProduct GroundTheory.Heights₂.Heights

noncomputable section

theorem HermitianExtension.degree_range_incl {K : Type} [Field K] [NumberField K]
    {E' E E'' : HermitianBundle.{0} K} (Y : HermitianExtension E' E E'') :
    E.degree (LinearMap.range Y.incl) = E'.arithDegree := by
  rw [HermitianBundle.degree_eq_arithDegree]
  symm
  refine LatticeLemmas.arithDegree_congr _ _ (LinearEquiv.ofInjective Y.incl Y.incl_injective)
    fun σ x y ↦ ?_
  rw [HermitianMetric.comap_inner, fibreMap_tmul, fibreMap_tmul]
  have h := Y.incl_isometric σ ((1 : ComplexAt σ) ⊗ₜ x) ((1 : ComplexAt σ) ⊗ₜ y)
  simp only [LinearMap.lTensor_tmul] at h
  exact h.symm

theorem S6.ExtensionDegree.proof : S6.ExtensionDegree.Statement := by
  intro K _ _ E' E E'' Y
  rw [HermitianBundle.degree_top_eq_arithDegree, HermitianBundle.degree_top_eq_arithDegree,
    HermitianExtension.degree_range_incl, Y.arithDegree_eq_add]
  ring

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField
open scoped nonZeroDivisors

theorem S6.SaturatedSpan.proof : S6.SaturatedSpan.Statement := by
  intro K _ _ M _ _ _ n ψ hψ G hsat
  obtain ⟨S, hS, hli⟩ := exists_set_linearIndependent_of_isDomain (𝓞 K) G
  rw [← Module.finrank_eq_rank] at hS
  obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hS
  let f : Fin (Module.finrank (𝓞 K) G) → G := fun i ↦ (e.symm i : G)
  have hf : LinearIndependent (𝓞 K) f := hli.comp _ e.symm.injective
  let φ : G →ₗ[𝓞 K] (Fin n → K) := ψ ∘ₗ G.subtype
  have hφ : Function.Injective φ := hψ.comp Subtype.val_injective
  let b : Fin (Module.finrank (𝓞 K) G) → Fin n → K := φ ∘ f
  have hbO : LinearIndependent (𝓞 K) b := hf.map' φ (LinearMap.ker_eq_bot.mpr hφ)
  have hb : LinearIndependent K b := (LinearIndependent.iff_fractionRing (𝓞 K) K).mp hbO
  refine ⟨b, hb, ?_⟩
  have hspanO : ∀ c : Fin (Module.finrank (𝓞 K) G) → 𝓞 K,
      φ (∑ j, c j • f j) ∈ Submodule.span K (Set.range b) := by
    intro c
    rw [map_sum]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    rw [map_smul, ← algebraMap_smul K (c j)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.mem_inf.mpr ⟨LinearMap.mem_range_self ψ x, ?_⟩
    have hnot : ¬ LinearIndependent (𝓞 K)
        (Fin.cons ⟨x, hx⟩ f : Fin (Module.finrank (𝓞 K) G + 1) → G) := by
      intro h
      have := h.fintype_card_le_finrank
      simp at this
    obtain ⟨s, hs0, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnot
    rw [Fin.sum_univ_succ] at hs0
    simp only [Fin.cons_zero, Fin.cons_succ] at hs0
    have ht : s 0 ≠ 0 := by
      intro h0
      rw [h0, zero_smul, zero_add] at hs0
      have hz := Fintype.linearIndependent_iff.mp hf (fun j ↦ s j.succ) hs0
      refine hi ?_
      cases i using Fin.cases with
      | zero => exact h0
      | succ j => exact hz j
    have key : s 0 • (⟨x, hx⟩ : G) = ∑ j, (-s j.succ) • f j := by
      simp only [neg_smul, Finset.sum_neg_distrib]
      exact eq_neg_of_add_eq_zero_left hs0
    have hmem := hspanO (fun j ↦ -s j.succ)
    rw [← key, map_smul] at hmem
    have hK : algebraMap (𝓞 K) K (s 0) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ht
    rw [← algebraMap_smul K (s 0)] at hmem
    have h2 := Submodule.smul_mem _ (algebraMap (𝓞 K) K (s 0))⁻¹ hmem
    rw [smul_smul, inv_mul_cancel₀ hK, one_smul] at h2
    exact h2
  · rintro y hy
    obtain ⟨⟨x, rfl⟩, hy⟩ := Submodule.mem_inf.mp hy
    have hy' : ψ x ∈ Submodule.span K (Set.range b) := hy
    obtain ⟨κ, hκ⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy'
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples (𝓞 K)⁰ Finset.univ κ
    choose a ha using fun j ↦ ht j (Finset.mem_univ j)
    have htx : (t : 𝓞 K) • x ∈ G := by
      have heq : ψ ((t : 𝓞 K) • x) = ψ (∑ j, a j • (f j : M)) := by
        rw [map_smul, ← hκ, map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [map_smul, ← algebraMap_smul K (a j), ha j, smul_assoc]
        rfl
      rw [hψ heq]
      exact Submodule.sum_mem _ fun j _ ↦ G.smul_mem _ (f j).2
    exact ⟨x, hsat _ x (nonZeroDivisors.coe_ne_zero t) htx, rfl⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights TensorProduct
open scoped nonZeroDivisors ComplexOrder

noncomputable section

theorem S6.MatrixSubDegree.genIndex_trans {G : Type*} [AddCommGroup G] {A B C : AddSubgroup G}
    (hCA : C ≤ A) (hCB : C ≤ B) (hBC : C.relIndex B ≠ 0) :
    genIndex A C = genIndex A B * genIndex B C := by
  unfold genIndex
  rw [AddSubgroup.relIndex_eq_one.mpr hCA, AddSubgroup.relIndex_eq_one.mpr hCB]
  have h1 := AddSubgroup.relIndex_mul_relIndex C (A ⊓ B) A (le_inf hCA hCB) inf_le_left
  have h2 := AddSubgroup.relIndex_mul_relIndex C (A ⊓ B) B (le_inf hCA hCB) inf_le_right
  have h1' : (A ⊓ B).relIndex A = B.relIndex A := by
    rw [inf_comm]; exact AddSubgroup.inf_relIndex_right B A
  have h2' : (A ⊓ B).relIndex B = A.relIndex B := AddSubgroup.inf_relIndex_right A B
  rw [h1'] at h1
  rw [h2'] at h2
  have hb : (A.relIndex B : ℝ) ≠ 0 := by
    intro h0
    apply hBC
    rw [← h2, Nat.cast_eq_zero.mp h0, mul_zero]
  rw [← h1, ← h2]
  push_cast
  field_simp

theorem S6.MatrixSubDegree.genIndex_map {G G' : Type*} [AddCommGroup G] [AddCommGroup G']
    (f : G →+ G') (hf : Function.Injective f) (A B : AddSubgroup G) :
    genIndex (A.map f) (B.map f) = genIndex A B := by
  unfold genIndex
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hf,
    AddSubgroup.relIndex_map_map_of_injective _ _ hf]

theorem S6.MatrixSubDegree.exists_smul_mem {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (𝓞 K) (Fin N → K)) (hspan : Submodule.span K (M : Set (Fin N → K)) = ⊤)
    {ι : Type*} [Fintype ι] (v : ι → Fin N → K) :
    ∃ t : 𝓞 K, t ≠ 0 ∧ ∀ i, algebraMap (𝓞 K) K t • v i ∈ M :=
  _root_.GroundTheory.Variant₂.N1.exists_smul_mem_family_of_span_eq_top M hspan v

theorem S6.MatrixSubDegree.finrank_satSub {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M] {r : ℕ} (u : Fin r → Fin N → K)
    (hu : LinearIndependent K u) (s : Fin r → satSub M u) (hs : LinearIndependent (𝓞 K) s) :
    Module.finrank (𝓞 K) (satSub M u) = r := by
  set W := Submodule.span K (Set.range u)
  let L : satSub M u →ₗ[𝓞 K] (Fin N → K) := M.subtype ∘ₗ (satSub M u).subtype
  have hLi : Function.Injective L := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  apply le_antisymm
  · apply Module.finrank_le_of_rank_le
    apply rank_le
    intro T hT
    have h0 := hT.map_injOn L hLi.injOn
    have h1 : LinearIndependent K (L ∘ fun i : T => (i : satSub M u)) :=
      (LinearIndependent.iff_fractionRing (𝓞 K) K).mp h0
    have hmem : ∀ i : T, L i ∈ W := fun i => (i : satSub M u).2
    have h2 : LinearIndependent K (fun i : T => (⟨L i, hmem i⟩ : W)) :=
      LinearIndependent.of_comp W.subtype h1
    have := h2.fintype_card_le_finrank
    rw [finrank_span_eq_card hu, Fintype.card_fin, Fintype.card_coe] at this
    exact this
  · have := hs.fintype_card_le_finrank
    simpa using this

theorem S6.MatrixSubDegree.gramAt_smul {K : Type} [Field K] {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ)
    (σ : K →+* ℂ) {ι : Type*} [Fintype ι] (u : ι → Fin N → K) (c : K) :
    gramAt h σ (fun i => c • u i) = ((‖σ c‖ ^ 2 : ℝ) : ℂ) • gramAt h σ u := by
  have he : ∀ v : Fin N → K, embVec σ (c • v) = σ c • embVec σ v := fun v => by
    funext k; simp [embVec]
  ext a b
  simp only [gramAt, he, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    Matrix.smul_apply, RCLike.star_def, ← mul_assoc]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem S6.MatrixSubDegree.log_gramDet {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M]
    (H : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (hH : ∀ σ, (H σ).PosDef)
    (hconj : ∀ σ, H (conjugate σ) = (H σ).map (starRingEnd ℂ)) {r : ℕ} (u : Fin r → Fin N → K)
    (hu : LinearIndependent K u) (c : K) (hc : c ≠ 0) (v : Fin r → M)
    (hv : ∀ i, (v i : Fin N → K) = c • u i) (σ : K →+* ℂ) :
    Real.log (gramDet (matrixBundle M H hH hconj).metric σ v) =
      r * (2 * Real.log ‖σ c‖) + Real.log (gramAt (H σ) σ u).det.re := by
  have hG : (gram ℂ fun i => fibreVec (matrixBundle M H hH hconj).metric σ (v i)) =
      ((‖σ c‖ ^ 2 : ℝ) : ℂ) • gramAt (H σ) σ u := by
    have e : (fun i => c • u i) = fun i => (v i : Fin N → K) := funext fun i => (hv i).symm
    rw [← S6.MatrixSubDegree.gramAt_smul, e]
    ext i j
    rw [gram_apply]
    exact matrixMetric_inner_one_tmul M H hH hconj σ (v i) (v j)
  have hD : 0 < (gramAt (H σ) σ u).det.re := by
    have := (LinesGramPosDef.full K N (H σ) σ (Fin r) u (hH σ) hu).det_pos
    exact (RCLike.pos_iff.mp this).1
  have hσc : ‖σ c‖ ≠ 0 := by
    rw [norm_ne_zero_iff, map_ne_zero]; exact hc
  simp only [GroundTheory.Heights₂.Heights.gramDet]
  rw [hG, det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Real.log_mul (pow_ne_zero _ (pow_ne_zero _ hσc)) hD.ne', Real.log_pow, Real.log_pow]
  push_cast
  ring

theorem S6.MatrixSubDegree.genIndex_span_smul {K : Type} [Field K] [NumberField K] {N r : ℕ}
    (u : Fin r → Fin N → K) (hu : LinearIndependent K u) (c : K) (hc : c ≠ 0) :
    genIndex (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup
        (Submodule.span (𝓞 K) (Set.range fun i => c • u i)).toAddSubgroup =
      |((Algebra.norm ℚ c : ℚ) : ℝ)| ^ r := by
  let φ : (Fin r → K) →ₗ[𝓞 K] (Fin N → K) :=
    (Fintype.linearCombination K u).restrictScalars (𝓞 K)
  have hφx : ∀ x, φ x = ∑ i, x i • u i := fun x => Fintype.linearCombination_apply K u x
  have hφ : Function.Injective φ := by
    intro x y hxy
    rw [hφx, hφx] at hxy
    have h0 : ∑ i, (x - y) i • u i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hxy, sub_self]
    funext i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hu _ h0 i)
  have hstd := LinesStdIndexDet.full K r (c • (1 : Matrix (Fin r) (Fin r) K))
    (by rw [det_smul, det_one, mul_one]; exact pow_ne_zero _ hc)
  have e1 : (⇑φ ∘ fun j : Fin r => (Pi.single j 1 : Fin r → K)) = u := by
    funext j
    show Fintype.linearCombination K u (Pi.single j 1) = u j
    rw [Fintype.linearCombination_apply_single, one_smul]
  have e2 : (⇑φ ∘ fun j : Fin r => (c • (1 : Matrix (Fin r) (Fin r) K)) *ᵥ Pi.single j 1) =
      fun i => c • u i := by
    funext j
    show Fintype.linearCombination K u ((c • (1 : Matrix (Fin r) (Fin r) K)) *ᵥ Pi.single j 1) =
      c • u j
    rw [Matrix.smul_mulVec, one_mulVec, map_smul, Fintype.linearCombination_apply_single,
      one_smul]
  have hB : Submodule.span (𝓞 K) (Set.range u) = (stdLattice K r).map φ := by
    rw [stdLattice, Submodule.map_span, ← Set.range_comp, e1]
  have hC : Submodule.span (𝓞 K) (Set.range fun i => c • u i) = (Submodule.span (𝓞 K)
      (Set.range fun j => (c • (1 : Matrix (Fin r) (Fin r) K)) *ᵥ Pi.single j 1)).map φ := by
    rw [Submodule.map_span, ← Set.range_comp, e2]
  rw [hB, hC, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    S6.MatrixSubDegree.genIndex_map _ hφ, hstd, det_smul, det_one, mul_one, Fintype.card_fin,
    map_pow, Rat.cast_pow, abs_pow]

theorem S6.MatrixSubDegree.card_quotient_eq_genIndex {R E G : Type*} [Ring R] [AddCommGroup E]
    [Module R E] [AddCommGroup G] [Module R G] (F : Submodule R E) (p : Submodule R F)
    (L : F →ₗ[R] G) (hL : Function.Injective L) :
    (Nat.card (F ⧸ p) : ℝ) = genIndex ((⊤ : Submodule R F).map L).toAddSubgroup (p.map L).toAddSubgroup := by
  rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    S6.MatrixSubDegree.genIndex_map _ hL, genIndex, Submodule.top_toAddSubgroup,
    AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_top_left, Nat.cast_one, div_one]
  rfl

theorem S6.MatrixSubDegree.card_quotient_pos {K : Type} [Field K] [NumberField K] {E : Type*}
    [AddCommGroup E] [Module (𝓞 K) E] (F : Submodule (𝓞 K) E) [Module.Finite (𝓞 K) F] {r : ℕ}
    (s : Fin r → F) (hs : LinearIndependent (𝓞 K) s) (hr : Module.finrank (𝓞 K) F = r) :
    (0 : ℝ) < Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s)) := by
  have := finite_quotient_span hs (by rw [Fintype.card_fin, hr])
  exact_mod_cast Nat.card_pos

theorem S6.MatrixSubDegree.proof : S6.MatrixSubDegree.Statement := by
  intro K _ _ N M _ H hH hconj hspan r u hu
  obtain ⟨t, ht, htM⟩ := S6.MatrixSubDegree.exists_smul_mem M hspan u
  have hτ : algebraMap (𝓞 K) K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ht
  have hfW : ∀ i, algebraMap (𝓞 K) K t • u i ∈ Submodule.span K (Set.range u) :=
    fun i => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let s : Fin r → satSub M u := fun i => ⟨⟨algebraMap (𝓞 K) K t • u i, htM i⟩, hfW i⟩
  let L : satSub M u →ₗ[𝓞 K] (Fin N → K) := M.subtype ∘ₗ (satSub M u).subtype
  have hL : Function.Injective L := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  have hLs : ⇑L ∘ s = fun i => algebraMap (𝓞 K) K t • u i := rfl
  have hs : LinearIndependent (𝓞 K) s := by
    refine LinearIndependent.of_comp L ?_
    rw [hLs]
    exact (LinearIndependent.iff_fractionRing (𝓞 K) K).mpr
      (hu.units_smul fun _ => Units.mk0 _ hτ)
  have hrank : (matrixBundle M H hH hconj).rank (satSub M u) = r :=
    S6.MatrixSubDegree.finrank_satSub M u hu s hs
  refine ⟨hrank, ?_⟩
  have hcard : Fintype.card (Fin r) = (matrixBundle M H hH hconj).rank (satSub M u) := by
    rw [Fintype.card_fin, hrank]
  rw [(matrixBundle M H hH hconj).degree_eq_of_linearIndependent (satSub M u) hs hcard]
  have hlog := fun σ => S6.MatrixSubDegree.log_gramDet M H hH hconj u hu _ hτ
    (fun i => (s i : M)) (fun i => rfl) σ
  simp_rw [hlog]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    LinesProductFormula.full K _ hτ]

  have hA : M ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K) =
      (⊤ : Submodule (𝓞 K) (satSub M u)).map L := by
    rw [Submodule.map_top, LinearMap.range_comp, Submodule.range_subtype, satSub,
      Submodule.map_comap_subtype]
  have hC : Submodule.span (𝓞 K) (Set.range fun i => algebraMap (𝓞 K) K t • u i) =
      (Submodule.span (𝓞 K) (Set.range s)).map L := by
    rw [Submodule.map_span, ← Set.range_comp, hLs]
  have hpos := S6.MatrixSubDegree.card_quotient_pos (satSub M u) s hs hrank
  rw [S6.MatrixSubDegree.card_quotient_eq_genIndex (satSub M u) _ L hL, ← hA, ← hC] at hpos
  erw [S6.MatrixSubDegree.card_quotient_eq_genIndex (satSub M u) _ L hL]
  rw [← hA]
  erw [← hC]
  have hBC := S6.MatrixSubDegree.genIndex_span_smul u hu _ hτ
  have hN : |((Algebra.norm ℚ (algebraMap (𝓞 K) K t) : ℚ) : ℝ)| ≠ 0 := by
    rw [abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]; exact hτ
  have hCA : (Submodule.span (𝓞 K) (Set.range fun i => algebraMap (𝓞 K) K t • u i)).toAddSubgroup ≤
      (M ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K)).toAddSubgroup := by
    rw [Submodule.toAddSubgroup_le, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨htM i, hfW i⟩
  have hCB : (Submodule.span (𝓞 K) (Set.range fun i => algebraMap (𝓞 K) K t • u i)).toAddSubgroup ≤
      (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup := by
    rw [Submodule.toAddSubgroup_le, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show algebraMap (𝓞 K) K t • u i ∈ Submodule.span (𝓞 K) (Set.range u)
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ t (Submodule.subset_span ⟨i, rfl⟩)
  have hrel : (Submodule.span (𝓞 K) (Set.range fun i => algebraMap (𝓞 K) K t • u i)).toAddSubgroup.relIndex
      (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup ≠ 0 := by
    intro h0
    apply pow_ne_zero r hN
    rw [← hBC, genIndex, h0, Nat.cast_zero, zero_div]
  have htrans := S6.MatrixSubDegree.genIndex_trans hCA hCB hrel
  rw [htrans, hBC] at hpos ⊢
  have hAB := left_ne_zero_of_mul hpos.ne'
  rw [Real.log_mul hAB (pow_ne_zero _ hN), Real.log_pow, subDegree]
  ring

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ComplexAt
open scoped nonZeroDivisors ComplexOrder

noncomputable section

namespace S6.QuotExtension

theorem schur_inner {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    (G : Matrix (m ⊕ k) (m ⊕ k) ℂ) (hA : IsUnit G.toBlocks₁₁.det) (β β' : m → ℂ) (γ γ' : k → ℂ)
    (h : ∀ i, (G *ᵥ Sum.elim β' γ') (Sum.inl i) = 0) :
    star (Sum.elim β γ) ⬝ᵥ (G *ᵥ Sum.elim β' γ') =
      star γ ⬝ᵥ ((G.toBlocks₂₂ - G.toBlocks₂₁ * G.toBlocks₁₁⁻¹ * G.toBlocks₁₂) *ᵥ γ') := by
  set A := G.toBlocks₁₁
  set B := G.toBlocks₁₂
  set C := G.toBlocks₂₁
  set D := G.toBlocks₂₂
  have hG : G = fromBlocks A B C D := (fromBlocks_toBlocks G).symm
  have hv : G *ᵥ Sum.elim β' γ' = Sum.elim (A *ᵥ β' + B *ᵥ γ') (C *ᵥ β' + D *ᵥ γ') := by
    rw [hG, fromBlocks_mulVec]
    rfl
  have h0 : A *ᵥ β' + B *ᵥ γ' = 0 := funext fun i => by simpa [hv] using h i
  have hβ : β' = -((A⁻¹ * B) *ᵥ γ') := by
    have hinv : A⁻¹ *ᵥ (A *ᵥ β') = β' := by rw [mulVec_mulVec, nonsing_inv_mul A hA, one_mulVec]
    rw [← hinv, eq_neg_iff_add_eq_zero, ← mulVec_mulVec, ← mulVec_add, h0, mulVec_zero]
  have hw : C *ᵥ β' + D *ᵥ γ' = (D - C * A⁻¹ * B) *ᵥ γ' := by
    rw [hβ, mulVec_neg, mulVec_mulVec, sub_mulVec, Matrix.mul_assoc]
    abel
  rw [hv, h0, hw]
  simp [dotProduct, Fintype.sum_sum_type]

variable {K : Type} [Field K] [NumberField K]

def embMat (σ : K →+* ℂ) {n : ℕ} {ι : Type*} (u : ι → Fin n → K) : Matrix (Fin n) ι ℂ :=
  Matrix.of fun r s => σ (u s r)

omit [NumberField K] in

theorem gramAt_eq {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    (u : ι → Fin n → K) : gramAt h σ u = (embMat σ u)ᴴ * h * embMat σ u := by
  ext s t
  simp only [gramAt, embVec, embMat, dotProduct, mulVec, Matrix.mul_apply, conjTranspose_apply,
    of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
  ring

omit [NumberField K] in

theorem inner_embMat {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    (u : ι → Fin n → K) (w w' : ι → ℂ) :
    star (embMat σ u *ᵥ w) ⬝ᵥ (h *ᵥ (embMat σ u *ᵥ w')) = star w ⬝ᵥ (gramAt h σ u *ᵥ w') := by
  rw [star_mulVec, ← dotProduct_mulVec, gramAt_eq, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

omit [NumberField K] in

theorem gramAt_mulVec_apply {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) {ι : Type*}
    [Fintype ι] (u : ι → Fin n → K) (w : ι → ℂ) (s : ι) :
    (gramAt h σ u *ᵥ w) s = star (embVec σ (u s)) ⬝ᵥ (h *ᵥ (embMat σ u *ᵥ w)) := by
  rw [gramAt_eq, ← mulVec_mulVec, ← mulVec_mulVec]
  simp only [mulVec, dotProduct, conjTranspose_apply, embMat, embVec, of_apply, Pi.star_apply]

theorem exists_smul_mem_idealLattice {n : ℕ} {a : Fin n → FractionalIdeal (𝓞 K)⁰ K}
    (ha : ∀ x, a x ≠ 0) (v : Fin n → K) : ∃ t : 𝓞 K, t ≠ 0 ∧ t • v ∈ idealLattice a := by
  classical
  choose e he0 hea using fun x => FractionalIdeal.exists_ne_zero_mem_isInteger (ha x)
  obtain ⟨c, hc0, hc⟩ := exists_common_denominator (M := Submodule.span (𝓞 K) {v})
    (Submodule.fg_span_singleton v)
  refine ⟨c * ∏ x, e x, mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr fun x _ => he0 x), ?_⟩
  rw [idealLattice, Submodule.mem_pi]
  intro x _
  obtain ⟨w, hw⟩ := hc v (Submodule.mem_span_singleton_self v) x
  rw [← Finset.mul_prod_erase Finset.univ e (Finset.mem_univ x)]
  have hx : ((c * (e x * ∏ y ∈ Finset.univ.erase x, e y)) • v) x =
      (w * ∏ y ∈ Finset.univ.erase x, e y) • algebraMap (𝓞 K) K (e x) := by
    rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, map_mul, hw]
    ring
  rw [hx]
  exact Submodule.smul_mem _ _ (hea x)

theorem coord_decomp {n m k : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (b : Fin m → Fin n → K)
    (c : Fin k → Fin n → K) (hli : LinearIndependent K (Sum.elim b c)) (hmk : m + k = n)
    (σ : K →+* ℂ) (x : Fibre σ (idealLattice a)) :
    ∃ β : Fin m → ℂ, latticeCoord σ (idealLattice a) x =
      embMat σ (Sum.elim b c) *ᵥ Sum.elim β (latticeCoord σ (quotLattice a b c hli hmk)
        ((quotProj a b c hli hmk).lTensor (ComplexAt σ) x)) := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul z v =>
    refine ⟨fun i => σ ((sumBasis b c hli hmk).repr v (Sum.inl i)) * (ofComplex σ).symm z, ?_⟩
    have hu : Sum.elim (fun i => σ ((sumBasis b c hli hmk).repr v (Sum.inl i)) *
        (ofComplex σ).symm z) (latticeCoord σ (quotLattice a b c hli hmk)
          ((quotProj a b c hli hmk).lTensor (ComplexAt σ) (z ⊗ₜ v))) =
        fun s => σ ((sumBasis b c hli hmk).repr v s) * (ofComplex σ).symm z := by
      funext s
      rcases s with i | j
      · rfl
      · rw [Sum.elim_inr, LinearMap.lTensor_tmul, latticeCoord_tmul]
        rfl
    rw [hu]
    funext r
    rw [latticeCoord_tmul]
    have hv := congrFun ((sumBasis b c hli hmk).sum_repr (v : Fin n → K)) r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sumBasis_apply] at hv
    simp only [mulVec, dotProduct, embMat, of_apply]
    rw [← hv, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_mul]
    ring
  | add x y hx hy =>
    obtain ⟨β, hβ⟩ := hx
    obtain ⟨β', hβ'⟩ := hy
    refine ⟨β + β', ?_⟩
    rw [map_add, map_add, map_add, hβ, hβ', ← mulVec_add, Sum.elim_add_add]

theorem orth_sub {n m : ℕ} {a : Fin n → FractionalIdeal (𝓞 K)⁰ K} (ha : ∀ x, a x ≠ 0)
    {d : (K →+* ℂ) → Fin n → ℝ} (hd : ∀ σ x, 0 < d σ x) (hc : ∀ σ x, d (conjugate σ) x = d σ x)
    (b : Fin m → Fin n → K) (σ : K →+* ℂ) (y : Fibre σ (idealLattice a))
    (hy : ∀ w : Fibre σ (subLattice a b), ((latticeBundle a d hd hc).metric.form σ).inner
      ((subLattice a b).subtype.lTensor (ComplexAt σ) w) y = 0) (i : Fin m) :
    star (embVec σ (b i)) ⬝ᵥ (diagMetric d σ *ᵥ latticeCoord σ (idealLattice a) y) = 0 := by
  obtain ⟨t, ht, htv⟩ := exists_smul_mem_idealLattice ha (b i)
  have hW : (⟨t • b i, htv⟩ : idealLattice a) ∈ subLattice a b :=
    Submodule.smul_of_tower_mem (Submodule.span K (Set.range b)) t
      (Submodule.subset_span ⟨i, rfl⟩)
  have h := hy ((1 : ComplexAt σ) ⊗ₜ ⟨_, hW⟩)
  rw [LinearMap.lTensor_tmul] at h
  have h' : star (latticeCoord σ (idealLattice a) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K]
      (⟨t • b i, htv⟩ : idealLattice a))) ⬝ᵥ
      (diagMetric d σ *ᵥ latticeCoord σ (idealLattice a) y) = 0 := h
  have hl : latticeCoord σ (idealLattice a) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K]
      (⟨t • b i, htv⟩ : idealLattice a)) = σ (t : K) • embVec σ (b i) := by
    funext r
    rw [latticeCoord_tmul]
    simp [embVec, Algebra.smul_def]
  have hσt : σ (t : K) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast ht
  rw [hl, star_smul, smul_dotProduct, smul_eq_mul] at h'
  exact (mul_eq_zero.mp h').resolve_left (by simpa using hσt)

end S6.QuotExtension

open S6.QuotExtension in

theorem S6.QuotExtension.proof : S6.QuotExtension.Statement := by
  intro K _ _ n a d hd hc ha m k b c hli hmk
  refine ⟨{ incl := (subLattice a b).subtype
            proj := quotProj a b c hli hmk
            incl_injective := (subLattice a b).injective_subtype
            proj_surjective := LinearMap.submoduleMap_surjective _ _
            exact := ?_
            incl_isometric := fun σ x y => rfl
            proj_coisometric := ?_ }, rfl, rfl⟩
  · show ∀ y : idealLattice a, quotProj a b c hli hmk y = 0 ↔ y ∈ Set.range (subLattice a b).subtype
    intro y
    have hker := KLinesQuotIndex.ker_coordProj (sumBasis b c hli hmk)
    have hr : (fun i => sumBasis b c hli hmk (Sum.inl i)) = b :=
      funext fun i => by rw [sumBasis_apply]; rfl
    rw [hr] at hker
    have h1 : quotProj a b c hli hmk y = 0 ↔
        coordProj (sumBasis b c hli hmk) (y : Fin n → K) = 0 := by
      rw [← Submodule.coe_eq_zero]
      exact Iff.rfl
    rw [h1, ← LinearMap.mem_ker, hker]
    constructor
    · intro h
      exact ⟨⟨y, h⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact w.2
  · intro σ x y _ hy
    obtain ⟨β, hx⟩ := coord_decomp a b c hli hmk σ x
    obtain ⟨β', hy'⟩ := coord_decomp a b c hli hmk σ y
    have hG := LinesGramPosDef.full K n _ σ _ _ (diagMetric_posDef hd σ) hli
    have hA : IsUnit (gramAt (diagMetric d σ) σ (Sum.elim b c)).toBlocks₁₁.det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (hG.submatrix Sum.inl_injective).isUnit
    change star (latticeCoord σ (quotLattice a b c hli hmk) _) ⬝ᵥ
        (schurMetric d b c σ *ᵥ latticeCoord σ (quotLattice a b c hli hmk) _) =
      star (latticeCoord σ (idealLattice a) x) ⬝ᵥ
        (diagMetric d σ *ᵥ latticeCoord σ (idealLattice a) y)
    rw [hx, hy', inner_embMat]
    refine (schur_inner _ hA _ _ _ _ fun i => ?_).symm
    rw [gramAt_mulVec_apply]
    exact (congrArg (fun v => star (embVec σ (b i)) ⬝ᵥ (diagMetric d σ *ᵥ v)) hy').symm.trans
      (orth_sub ha hd hc b σ y hy i)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

theorem S6.LatticeAsBundle.full : S6.LatticeAsBundle.Statement :=
  S6.LatticeAsBundle.proof S6.MatrixSubDegree.proof S6.QuotExtension.proof S6.QuotDegree.proof

theorem S6.BundleCoordinates.full : S6.BundleCoordinates.Statement :=
  S6.BundleCoordinates.proof S6.LineCoordinates.proof S6.CoordinateDegree.proof
    S6.QuotientDegreeSplit.proof S6.ExtensionDegree.proof S6.SaturatedSpan.proof

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end
