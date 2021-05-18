import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- + (Addition)
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

-- Addition: Right Identity Zero
+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc x) =
  begin
    suc x + zero
  ≡⟨⟩
    suc (x + zero)
  ≡⟨ cong suc (+-identityʳ x) ⟩
    suc x
  ∎

-- Addition: Preposition of Suc
+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
   zero + suc n
 ≡⟨⟩
   suc n
 ≡⟨⟩
   suc (zero + n)
 ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

-- * (Multiplication)
_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n  = n + (m * n)

-- Multiplication: Right Identity Zero
*-identityʳ : ∀ (n : ℕ) → zero * n ≡ zero
*-identityʳ zero =
  begin
    zero * zero
  ≡⟨⟩
    zero
  ∎
*-identityʳ (suc x) =
  begin
    zero * suc x
  ≡⟨⟩
    zero
  ∎

-- Multiplication: Preposition of Suc
*-suc : ∀ (m n : ℕ) → (suc m) * n ≡ n + (m * n)
*-suc zero n rewrite *-identityʳ n = refl
*-suc (suc m) n rewrite *-suc m n = refl
