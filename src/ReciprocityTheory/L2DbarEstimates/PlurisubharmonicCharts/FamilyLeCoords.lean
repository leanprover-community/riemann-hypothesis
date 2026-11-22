module

public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

noncomputable section

def ovl {n : ℕ} {Y ι : Type*} [TopologicalSpace Y] (chart : ι → OpenPartialHomeomorph Y (V n))
    (i j : ι) : Set (V n) :=
  (chart i).target ∩ (chart i).symm ⁻¹' (chart j).source

structure WeightedAtlas (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    (ι : Type*) (La : Type*) [AddCommGroup La] where

  chart : ι → OpenPartialHomeomorph Y (V n)

  pick : Y → ι
  mem_pick : ∀ y, y ∈ (chart (pick y)).source

  holo_trans : ∀ i j, DifferentiableOn ℂ (chart j ∘ (chart i).symm) (ovl chart i j)

  g : La → ι → ι → Y → ℂ
  holo_g : ∀ la i j, DifferentiableOn ℂ (g la i j ∘ (chart i).symm) (ovl chart i j)
  g_ne : ∀ la i j y, y ∈ (chart i).source → y ∈ (chart j).source → g la i j y ≠ 0
  g_cocycle : ∀ la i j k y, y ∈ (chart i).source → y ∈ (chart j).source →
    y ∈ (chart k).source → g la i k y = g la i j y * g la j k y
  g_add : ∀ la mu i j y, y ∈ (chart i).source → y ∈ (chart j).source →
    g (la + mu) i j y = g la i j y * g mu i j y

  ph : La → ι → Y → ℝ
  smooth_ph : ∀ la i, ContDiffOn ℝ ∞ (ph la i ∘ (chart i).symm) (chart i).target
  ph_add : ∀ la mu i y, y ∈ (chart i).source → ph (la + mu) i y = ph la i y + ph mu i y
  ph_trans : ∀ la i j y, y ∈ (chart i).source → y ∈ (chart j).source →
    ph la j y = ph la i y - Real.log (‖g la i j y‖ ^ 2)

  kap : La
  g_kap : ∀ i j y, y ∈ (chart i).source → y ∈ (chart j).source →
    g kap i j y = (fderiv ℂ (chart j ∘ (chart i).symm) (chart i y)).det

  mu : Measure Y
  mu_chart : ∀ i (A : Set Y), MeasurableSet A → A ⊆ (chart i).source →
    mu A = ∫⁻ v in chart i '' A, ENNReal.ofReal (Real.exp (ph kap i ((chart i).symm v)))

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

def IsSecOn (A : WeightedAtlas n Y ι La) (la : La) (U : Set Y) (s : ι → Y → ℂ) : Prop :=
  (∀ i, DifferentiableOn ℂ (s i ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)) ∧
  ∀ i j y, y ∈ U → y ∈ (A.chart i).source → y ∈ (A.chart j).source → s i y = A.g la i j y * s j y

def IsSec (A : WeightedAtlas n Y ι La) (la : La) (s : ι → Y → ℂ) : Prop :=
  A.IsSecOn la Set.univ s

def IsSSec (A : WeightedAtlas n Y ι La) (la : La) (s : ι → Y → ℂ) : Prop :=
  (∀ i, ContDiffOn ℝ ∞ (s i ∘ (A.chart i).symm) (A.chart i).target) ∧
  ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → s i y = A.g la i j y * s j y

def IsFrameOn (A : WeightedAtlas n Y ι La) (la : La) (U : Set Y) (s : ι → Y → ℂ) : Prop :=
  A.IsSecOn la U s ∧ ∀ y ∈ U, s (A.pick y) y ≠ 0

def SmoothFn (A : WeightedAtlas n Y ι La) (f : Y → ℝ) : Prop :=
  ∀ i, ContDiffOn ℝ ∞ (f ∘ (A.chart i).symm) (A.chart i).target

def nsq (A : WeightedAtlas n Y ι La) (la : La) (s : ι → Y → ℂ) (y : Y) : ℝ :=
  ‖s (A.pick y) y‖ ^ 2 * Real.exp (-A.ph la (A.pick y) y)

def sqn {N : ℕ} (A : WeightedAtlas n Y ι La) (la : La) (w : Fin N → ι → Y → ℂ) (y : Y) : ℝ :=
  ∑ k, A.nsq la (w k) y

def leviAt (A : WeightedAtlas n Y ι La) (i : ι) (f : Y → ℝ) (y : Y) (ξ : Fin n → ℂ) : ℝ :=
  (leviV n (fun v => ((f ((A.chart i).symm v) : ℝ) : ℂ)) (A.chart i y) ξ).re

def Pos (A : WeightedAtlas n Y ι La) (la : La) (ps : Y → ℝ) : Prop :=
  ∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ,
    0 ≤ A.leviAt i (fun x => A.ph la i x + ps x) y ξ

def zeroSet {N : ℕ} (A : WeightedAtlas n Y ι La) (s : Fin N → ι → Y → ℂ) : Set Y :=
  {y | ∀ k, s k (A.pick y) y = 0}

def zLoc (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (i : ι) :
    V n → V n :=
  fun v => WithLp.toLp 2 (fun k => s k i ((A.chart i).symm v) / w0 i ((A.chart i).symm v))

def zmap (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (y : Y) : V n :=
  WithLp.toLp 2 (fun k => s k (A.pick y) y / w0 (A.pick y) y)

def IsCoordAt (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (P : Y) :
    Prop :=
  (fderiv ℂ (A.zLoc w0 s (A.pick P)) (A.chart (A.pick P) P)).det ≠ 0

end WeightedAtlas

def multiLe (n j : ℕ) : Finset (Fin n → ℕ) :=
  (Finset.range (j + 1)).biUnion (fun d => Finset.Nat.antidiagonalTuple n d)

end

end ReciprocityTheory.L2DbarEstimates.Y
