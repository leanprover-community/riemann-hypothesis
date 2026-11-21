import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.T

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

universe u

section Defs

variable {o : Type*} {Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {ι κ : Type*}
  {E : Type*} [AddCommGroup E] [Module Ω E] {r : ℕ}

variable {x : ι → Ω}

def dualLat (B : ChartBundle o x r E) (i : ι) : Set (E →ₗ[Ω] Ω) :=
  {ψ | ∀ v ∈ B.lat i, ψ v ∈ chartRing o x i}

def IsTwistedDualSec (B : ChartBundle o x r E) (φ : κ → E →ₗ[Ω] Ω) : Prop :=
  ∀ i, x i ≠ 0 → ∀ k, ∀ v ∈ B.lat i, φ k v ∈ lineLat o x 1 i

def IsTwistedDualGen [Fintype κ] (B : ChartBundle o x r E) (φ : κ → E →ₗ[Ω] Ω) : Prop :=
  ∀ i, x i ≠ 0 → ∀ ψ ∈ dualLat B i, ∃ c : κ → Ω, (∀ k, c k ∈ chartRing o x i) ∧
    ψ = ∑ k, c k • (x i)⁻¹ • φ k

variable {Φ : Type*} [Field Φ] [Algebra Ω Φ]

def detE (e : Module.Basis (Fin 2) Ω E) (u w : E) : Ω :=
  e.repr u 0 * e.repr w 1 - e.repr u 1 * e.repr w 0

def lineVal (e : Module.Basis (Fin 2) Ω E) (ψ : E →ₗ[Ω] Ω) (a : Φ) : Φ :=
  algebraMap Ω Φ (ψ (e 0)) + a * algebraMap Ω Φ (ψ (e 1))

def lineDet (e : Module.Basis (Fin 2) Ω E) (a : Φ) (u : E) : Φ :=
  algebraMap Ω Φ (e.repr u 1) - a * algebraMap Ω Φ (e.repr u 0)

def powVec (x : ι → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) {m : ℕ}
    (a : Fin m → Φ) : ι × (Fin m → κ) → Φ :=
  segreJoin (fun i => algebraMap Ω Φ (x i)) (fun k => ∏ j, lineVal e (φ (k j)) (a j))

abbrev projVec (x : ι → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a : Φ) :
    ι × (Fin 1 → κ) → Φ :=
  powVec x e φ ![a]

abbrev fibreSqVec (x : ι → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a : Fin 2 → Φ) :
    ι × (Fin 2 → κ) → Φ :=
  powVec x e φ a

variable [Algebra o Φ] [IsScalarTower o Ω Φ]

def tautDualGens (B : ChartBundle o x r E) (e : Module.Basis (Fin 2) Ω E) (a : Φ) (i : ι) :
    Set Φ :=
  {F | ∃ ψ ∈ dualLat B i, F = lineVal e ψ a}

def detGens (B : ChartBundle o x r E) (e : Module.Basis (Fin 2) Ω E) (i : ι) : Set Φ :=
  {F | ∃ u ∈ B.lat i, ∃ w ∈ B.lat i, F = algebraMap Ω Φ (detE e u w)}

def diagBundleLat (B : ChartBundle o x r E) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a : Fin 2 → Φ) (i : ι) (k : Fin 2 → κ) : Submodule (chartRing o (fibreSqVec x e φ a) (i, k)) Φ :=
  Submodule.span _ {F | ∃ F₀ ∈ tautDualGens B e (a 0) i, ∃ F₁ ∈ tautDualGens B e (a 1) i,
    ∃ δ ∈ detGens B e i, F = F₀ * F₁ * δ}

def diagSec (a : Fin 2 → Φ) : Φ := a 1 - a 0

def pullThrough (x : ι → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a : Fin 2 → Φ)
    (N : ι → AddSubgroup Ω) (j : Fin 2) (i : ι) (k : Fin 2 → κ) :
    Submodule (chartRing o (fibreSqVec x e φ a) (i, k)) Φ :=
  Submodule.span _ (Submodule.span (chartRing o (projVec x e φ (a j)) (i, ![k j]))
    (algebraMap Ω Φ '' (N i : Set Ω)) : Set Φ)

def IsFrameOn (B : ChartBundle o x r E) (i : ι) (f : Ω) (b : Fin 2 → E) : Prop :=
  f ∈ chartRing o x i ∧ f ≠ 0 ∧ LinearIndependent Ω b ∧
    ∀ v, (∃ n : ℕ, f ^ n • v ∈ B.lat i) ↔
      ∃ c : Fin 2 → Ω, (∀ q, ∃ n : ℕ, f ^ n * c q ∈ chartRing o x i) ∧ v = ∑ q, c q • b q

def frameRing (x : ι → Ω) (i : ι) (f : Ω) : Subalgebra o Ω :=
  Algebra.adjoin o ((chartRing o x i : Set Ω) ∪ {f⁻¹})

def frameCoord (e : Module.Basis (Fin 2) Ω E) (b : Fin 2 → E) (a : Φ) : Φ :=
  -lineDet e a (b 0) / lineDet e a (b 1)

def frameGen (e : Module.Basis (Fin 2) Ω E) (b : Fin 2 → E) (a : Fin 2 → Φ) : Φ :=
  lineDet e (a 0) (b 1) * lineDet e (a 1) (b 1) / algebraMap Ω Φ (detE e (b 0) (b 1))

def frameChartRing (x : ι → Ω) (e : Module.Basis (Fin 2) Ω E) (b : Fin 2 → E) (a : Fin 2 → Φ)
    (i : ι) (f : Ω) : Subalgebra o Φ :=
  Algebra.adjoin o (algebraMap Ω Φ '' (frameRing (o := o) x i f : Set Ω) ∪ Set.range fun j => frameCoord e b (a j))

def frameAlpha (e : Module.Basis (Fin 2) Ω E) (b : Fin 2 → E) (a : Φ) : Φ :=
  lineDet e a (b 1) / algebraMap Ω Φ (detE e (b 0) (b 1))

def frameUnit (x : ι → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (b : Fin 2 → E)
    (a : Fin 2 → Φ) (i : ι) (k : Fin 2 → κ) (j : Fin 2) : Φ :=
  lineVal e (φ (k j)) (a j) / (algebraMap Ω Φ (x i) * frameAlpha e b (a j))

end Defs

section Statements

variable {o : Type*} {Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {ι κ : Type*} [Fintype κ]
  {E : Type*} [AddCommGroup E] [Module Ω E] {x : ι → Ω}
  {Φ : Type*} [Field Φ] [Algebra Ω Φ] [Algebra o Φ] [IsScalarTower o Ω Φ]

def PowChartStatement (B : ChartBundle o x 2 E) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) :
    Prop :=
  IsScalarTower o Ω Φ → IsTwistedDualSec B φ → IsTwistedDualGen B φ → ∀ (m : ℕ) (a : Fin m → Φ), AlgebraicIndependent Ω a →
    ∀ i (k : Fin m → κ), x i ≠ 0 → (∀ j, φ (k j) ≠ 0) →
      chartRing o (powVec x e φ a) (i, k) = Algebra.adjoin o (algebraMap Ω Φ '' (chartRing o x i : Set Ω) ∪
        ⋃ j, {y | ∃ ψ ∈ dualLat B i, y = algebraMap Ω Φ (x i) * lineVal e ψ (a j) / lineVal e (φ (k j)) (a j)})

def DiagSecStatement (B : ChartBundle o x 2 E) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) :
    Prop :=
  IsScalarTower o Ω Φ → IsTwistedDualSec B φ → IsTwistedDualGen B φ → ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
    ∀ i k, x i ≠ 0 → (∀ j, φ (k j) ≠ 0) → diagSec a ∈ diagBundleLat B e φ a i k

def FrameChartStatement (B : ChartBundle o x 2 E) (e : Module.Basis (Fin 2) Ω E) : Prop :=
  IsScalarTower o Ω Φ → ∀ (a : Fin 2 → Φ), AlgebraicIndependent Ω a → ∀ i f (b : Fin 2 → E), x i ≠ 0 → IsFrameOn B i f b →
    AlgebraicIndependent Ω (fun j => frameCoord e b (a j)) ∧
    (∀ F₀ ∈ tautDualGens B e (a 0) i, ∀ F₁ ∈ tautDualGens B e (a 1) i, ∀ δ ∈ detGens (Φ := Φ) B e i,
      F₀ * F₁ * δ / frameGen e b a ∈ frameChartRing (o := o) x e b a i f) ∧
    (∃ n : ℕ, algebraMap Ω Φ (f ^ n) * frameGen e b a ∈
      Submodule.span (frameChartRing (o := o) x e b a i f) {F | ∃ F₀ ∈ tautDualGens B e (a 0) i,
        ∃ F₁ ∈ tautDualGens B e (a 1) i, ∃ δ ∈ detGens B e i, F = F₀ * F₁ * δ}) ∧
    diagSec a = frameGen e b a * (frameCoord e b (a 1) - frameCoord e b (a 0))

def FrameLocStatement (B : ChartBundle o x 2 E) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) :
    Prop :=
  IsScalarTower o Ω Φ → IsTwistedDualSec B φ → IsTwistedDualGen B φ → ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
    ∀ i f (b : Fin 2 → E) (k : Fin 2 → κ), x i ≠ 0 → IsFrameOn B i f b → (∀ j, φ (k j) ≠ 0) →
      Algebra.adjoin o ((frameChartRing (o := o) x e b a i f : Set Φ) ∪
          Set.range fun j => (frameUnit x e φ b a i k j)⁻¹) =
        Algebra.adjoin o ((chartRing o (fibreSqVec x e φ a) (i, k) : Set Φ) ∪
          {(algebraMap Ω Φ f)⁻¹} ∪ Set.range (frameUnit x e φ b a i k))

def BaseLineStatement (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) : Prop :=
  IsScalarTower o Ω Φ → ∀ (a : Fin 2 → Φ), AlgebraicIndependent Ω a → ∀ (N : ι → AddSubgroup Ω) i k, x i ≠ 0 →
    (∀ j, φ (k j) ≠ 0) → pullThrough (o := o) x e φ a N 0 i k = pullThrough x e φ a N 1 i k

def threeFrames (b : Fin 2 → E) : Fin 3 → Fin 2 → E :=
  ![b, ![b 1, b 0], ![b 0, b 0 + b 1]]

def FrameCoverStatement (B : ChartBundle o x 2 E) : Prop :=
  (∀ i f (b : Fin 2 → E), IsFrameOn B i f b → ∀ c, IsFrameOn B i f (threeFrames b c)) ∧
  ∀ (K : Type u) [Field K] (p : Fin 2 → Fin 2 → K), (∀ j, p j ≠ 0) → ∃ c : Fin 3, ∀ j,
    p j 0 * (![![0, 1], ![1, 0], ![1, 1]] c : Fin 2 → K) 1 -
      p j 1 * (![![0, 1], ![1, 0], ![1, 1]] c : Fin 2 → K) 0 ≠ 0

end Statements

def diagIdeal (A : Type*) [CommRing A] : Ideal (MvPolynomial (Fin 2) A) :=
  RingHom.ker (aeval fun _ => Polynomial.X : MvPolynomial (Fin 2) A →ₐ[A] Polynomial A)

def DiagDivisorStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A],
    Ideal.span {(X 0 - X 1 : MvPolynomial (Fin 2) A)} = diagIdeal A ∧ (diagIdeal A).IsPrime ∧
    ∀ [(diagIdeal A).IsPrime], Module.length (Localization.AtPrime (diagIdeal A))
      (Localization.AtPrime (diagIdeal A) ⧸
        Ideal.span {algebraMap (MvPolynomial (Fin 2) A) (Localization.AtPrime (diagIdeal A)) (X 0 - X 1)}) = 1

def InhabitStatement : Prop :=
  ∃ (B : ChartBundle ℤ (fun _ : Unit => (1 : ℚ)) 2 (Fin 2 → ℚ))
    (φ : Fin 2 → (Fin 2 → ℚ) →ₗ[ℚ] ℚ) (e : Module.Basis (Fin 2) ℚ (Fin 2 → ℚ)),
    (∀ k, φ k ≠ 0) ∧ B.lat () ≠ ⊤ ∧ IsTwistedDualSec B φ ∧ IsTwistedDualGen B φ ∧
    ∃ a : Fin 2 → FractionRing (MvPolynomial (Fin 2) ℚ), AlgebraicIndependent ℚ a ∧
      chartRing ℤ (projVec (fun _ : Unit => (1 : ℚ)) e φ (a 0)) ((), ![0]) =
        Algebra.adjoin ℤ {a 0}

end ReciprocityTheory.ChartRestriction.G.AI.T
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.T

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

universe u

inductive WBlk | base | det | line0 | line1
  deriving DecidableEq

instance : Fintype WBlk := ⟨{.base, .det, .line0, .line1}, by intro k; cases k <;> simp⟩

inductive YBlk | base | det | line
  deriving DecidableEq

instance : Fintype YBlk := ⟨{.base, .det, .line}, by intro k; cases k <;> simp⟩

def wwIdx (ι ν κ : Type u) : WBlk → Type u
  | .base => ι
  | .det => ν
  | .line0 => κ
  | .line1 => κ

def yyIdx (ι ν κ : Type u) : YBlk → Type u
  | .base => ι
  | .det => ν
  | .line => κ

instance wwIdx.fintype {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ] :
    (k : WBlk) → Fintype (wwIdx ι ν κ k)
  | .base => inferInstanceAs (Fintype ι)
  | .det => inferInstanceAs (Fintype ν)
  | .line0 => inferInstanceAs (Fintype κ)
  | .line1 => inferInstanceAs (Fintype κ)

instance yyIdx.fintype {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ] :
    (k : YBlk) → Fintype (yyIdx ι ν κ k)
  | .base => inferInstanceAs (Fintype ι)
  | .det => inferInstanceAs (Fintype ν)
  | .line => inferInstanceAs (Fintype κ)

def multiConeMap {K : Type*} {ι : K → Type*} {Φ : Type*} [Field Φ] (c : (Σ k, ι k) → Φ) :
    MvPolynomial (Σ k, ι k) ℤ →+* MvPolynomial K Φ :=
  eval₂Hom (Int.castRingHom _) fun p => C (c p) * X p.1

section Models

variable {Ω : Type*} [Field Ω] {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ]
  {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]

def IsTwistedDetGen {x : ι → Ω} (B : ChartBundle ℤ x 2 E) (e : Module.Basis (Fin 2) Ω E) (δ : ν → Ω) :
    Prop :=
  ∀ i, x i ≠ 0 →
    (∀ l, δ l ∈ Submodule.span (chartRing ℤ x i)
      {d | ∃ u ∈ B.lat i, ∃ w ∈ B.lat i, d = x i * detE e u w}) ∧
    ∀ u ∈ B.lat i, ∀ w ∈ B.lat i,
      detE e u w ∈ Submodule.span (chartRing ℤ x i) (Set.range fun l => (x i)⁻¹ * δ l)

def wwCoord (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ) :
    (Σ k, wwIdx ι ν κ k) → Φ
  | ⟨.base, i⟩ => algebraMap Ω Φ (x i)
  | ⟨.det, l⟩ => algebraMap Ω Φ (δ l)
  | ⟨.line0, k⟩ => lineVal e (φ k) a₀
  | ⟨.line1, k⟩ => lineVal e (φ k) a₁

def yyCoord (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a : Φ) :
    (Σ k, yyIdx ι ν κ k) → Φ
  | ⟨.base, i⟩ => algebraMap Ω Φ (x i)
  | ⟨.det, l⟩ => algebraMap Ω Φ (δ l)
  | ⟨.line, k⟩ => lineVal e (φ k) a

def wwIdeal (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ) :
    Ideal (MRing (wwIdx ι ν κ)) :=
  RingHom.ker (multiConeMap (wwCoord x δ e φ a₀ a₁))

def yyIdeal (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a : Φ) :
    Ideal (MRing (yyIdx ι ν κ)) :=
  RingHom.ker (multiConeMap (yyCoord x δ e φ a))

def yyEmb (j : Fin 2) : (Σ k, yyIdx ι ν κ k) → (Σ k, wwIdx ι ν κ k)
  | ⟨.base, i⟩ => ⟨.base, i⟩
  | ⟨.det, l⟩ => ⟨.det, l⟩
  | ⟨.line, k⟩ => if j = 0 then ⟨.line0, k⟩ else ⟨.line1, k⟩

def baseIdeal (x : ι → Ω) : Ideal (MRing (fun _ : Unit => ι)) :=
  RingHom.ker (multiConeMap (fun p : (Σ _ : Unit, ι) => x p.2))

def WWArithVarStatement {x : ι → Ω} (B : ChartBundle ℤ x 2 E) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω) : Prop :=
  IsTwistedDualSec B φ → IsTwistedDualGen B φ → IsTwistedDetGen B e δ →
    ∀ D : ℕ, IsArithVar (baseIdeal x) D → ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
      (∀ j, IsArithVar (yyIdeal x δ e φ (a j)) (D + 1)) ∧
      IsArithVar (wwIdeal x δ e φ (a 0) (a 1)) (D + 2) ∧
      IsArithVar (wwIdeal x δ e φ (a 0) (a 0)) (D + 1)

def wwDeg (n m : ℕ) : WBlk → ℕ
  | .base => n
  | _ => m

def YYComapStatement (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) :
    Prop :=
  ∀ (a : Fin 2 → Φ) (j : Fin 2),
    (wwIdeal x δ e φ (a 0) (a 1)).comap (rename (yyEmb j) : MRing (yyIdx ι ν κ) →ₐ[ℤ] _).toRingHom =
      yyIdeal x δ e φ (a j)

def toZCycle {α : Type*} (z : α →₀ ℕ) : α →₀ ℤ :=
  Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) z

def DiagDivStatement {x : ι → Ω} (B : ChartBundle ℤ x 2 E) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω) : Prop :=
  IsTwistedDualSec B φ → IsTwistedDualGen B φ → IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
    ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
      (∃ (n : ℕ) (g h : MRing (wwIdx ι ν κ)), IsMultiHomog g (wwDeg n 1) ∧
        IsMultiHomog h (wwDeg (n + 3) 0) ∧ h ∉ wwIdeal x δ e φ (a 0) (a 1) ∧
        aeval (wwCoord x δ e φ (a 0) (a 1)) g = diagSec a * aeval (wwCoord x δ e φ (a 0) (a 1)) h) ∧
      ∀ (n : ℕ) (g h : MRing (wwIdx ι ν κ)), IsMultiHomog g (wwDeg n 1) →
        IsMultiHomog h (wwDeg (n + 3) 0) → h ∉ wwIdeal x δ e φ (a 0) (a 1) →
        aeval (wwCoord x δ e φ (a 0) (a 1)) g = diagSec a * aeval (wwCoord x δ e φ (a 0) (a 1)) h →
          toZCycle (divCycle (wwIdeal x δ e φ (a 0) (a 1)) g) -
              toZCycle (divCycle (wwIdeal x δ e φ (a 0) (a 1)) h) =
            Finsupp.single (wwIdeal x δ e φ (a 0) (a 0)) 1

end Models

section Degrees

def unitDeg {K : Type*} [DecidableEq K] (k : K) : K → ℤ := Pi.single k 1

def twoXiDeg (j : Fin 2) : WBlk → ℤ :=
  3 • unitDeg .base - unitDeg .det - 2 • unitDeg (if j = 0 then .line0 else .line1)

def llDeg : WBlk → ℤ :=
  unitDeg .det + unitDeg .line0 + unitDeg .line1 - 3 • unitDeg .base

theorem two_llDeg : 2 • llDeg = -(twoXiDeg 0 + twoXiDeg 1) := by
  funext k
  cases k <;> simp [llDeg, twoXiDeg, unitDeg]

def pullDeg (j : Fin 2) (c : YBlk → ℤ) : WBlk → ℤ
  | .base => c .base
  | .det => c .det
  | .line0 => if j = 0 then c .line else 0
  | .line1 => if j = 0 then 0 else c .line

theorem pullDeg_base (c : YBlk → ℤ) (hc : c .line = 0) : pullDeg 0 c = pullDeg 1 c := by
  funext k
  cases k <;> simp [pullDeg, hc]

def twoXiDegY : YBlk → ℤ
  | .base => 3
  | .det => -1
  | .line => -2


end Degrees

section Diagonal

variable {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ]

def IsHermPull (j : Fin 2) (A : HermLine (yyIdx ι ν κ)) (A' : HermLine (wwIdx ι ν κ)) : Prop :=
  A'.a = pullDeg j A.a ∧ ∀ z, A'.h z = A.h fun p => z (yyEmb j p)

variable (ι ν κ) in

def HermPullStatement : Prop :=
  ∀ (j : Fin 2) (A : HermLine (yyIdx ι ν κ)), ∃ A' : HermLine (wwIdx ι ν κ),
    IsHermPull j A A' ∧ (IsSmoothHerm A → IsSmoothHerm A')

def DiagPullStatement {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    {Φ : Type*} [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) : Prop :=
  ∀ a₀ : Φ,
    (∀ (s : MRing (yyIdx ι ν κ)) (d : YBlk → ℕ), IsMultiHomog s d →
      divCycle (wwIdeal x δ e φ a₀ a₀) (rename (yyEmb 0) s) =
        divCycle (wwIdeal x δ e φ a₀ a₀) (rename (yyEmb 1) s)) ∧
    (∀ (A : HermLine (yyIdx ι ν κ)) (A₀ A₁ : HermLine (wwIdx ι ν κ)), IsHermPull 0 A A₀ →
      IsHermPull 1 A A₁ → ∀ z ∈ mcPts (wwIdeal x δ e φ a₀ a₀), ∃ c : ℂ, c ≠ 0 ∧
        (∀ k : κ, z ⟨.line1, k⟩ = c * z ⟨.line0, k⟩) ∧ A₁.h z = ‖c‖ ^ A.a .line * A₀.h z) ∧
    (∀ (s : MRing (yyIdx ι ν κ)) (d : YBlk → ℕ), IsMultiHomog s d →
      ∀ (A : HermLine (yyIdx ι ν κ)) (A₀ A₁ : HermLine (wwIdx ι ν κ)), (∀ k, A.a k = d k) →
        IsHermPull 0 A A₀ → IsHermPull 1 A A₁ → ∀ z ∈ mcPts (wwIdeal x δ e φ a₀ a₀),
          logNorm A₀ (rename (yyEmb 0) s) z = logNorm A₁ (rename (yyEmb 1) s) z)

end Diagonal

def InhabitWWStatement : Prop :=
  ∃ (B : ChartBundle ℤ (fun _ : PUnit.{1} => (1 : ℚ)) 2 (Fin 2 → ℚ))
    (φ : PUnit.{1} ⊕ PUnit.{1} → (Fin 2 → ℚ) →ₗ[ℚ] ℚ) (e : Module.Basis (Fin 2) ℚ (Fin 2 → ℚ)),
    IsTwistedDualSec B φ ∧ IsTwistedDualGen B φ ∧
    IsTwistedDetGen (ν := PUnit.{1}) B e (fun _ => 1) ∧
    ∃ a : Fin 2 → FractionRing (MvPolynomial (Fin 2) ℚ), AlgebraicIndependent ℚ a ∧
      wwIdeal (fun _ : PUnit.{1} => (1 : ℚ)) (fun _ : PUnit.{1} => (1 : ℚ)) e φ (a 0) (a 1) ≠
        wwIdeal (fun _ : PUnit.{1} => (1 : ℚ)) (fun _ : PUnit.{1} => (1 : ℚ)) e φ (a 0) (a 0)

def InhabitBaseStatement : Prop :=
  IsArithVar (baseIdeal (fun _ : PUnit.{1} => (1 : ℚ))) 1

end ReciprocityTheory.ChartRestriction.G.AI.T
end
end
