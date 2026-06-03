import Mathlib.Data.List.Basic
import Mathlib.Data.List.Perm
import Mathlib.Data.List.Sort
import Mathlib.Tactic

open List

/-
-- 1. Подготовительный этап
-- 1.1. Задать тип элементов с линейным порядком и разрешимым сравнением.
-- 1.2. Импортировать необходимые библиотеки (списки, перестановки, порядок, тактики).

-- 2. Определение вспомогательной функции split
-- 2.1. Реализовать split, которая делит список на две примерно равные части.
-- 2.2. Доказать: сумма длин двух частей равна длине исходного списка.
-- 2.3. Доказать: конкатенация двух частей является перестановкой исходного списка.
-- 2.4. Доказать: если длина списка ≥ 2, то каждая часть строго короче исходного списка .

-- 3. Определение функции merge
-- 3.1. Реализовать merge, сливающую два отсортированных списка в один.
-- 3.2. Доказать: если оба входных списка отсортированы, то результат merge тоже отсортирован.
-- 3.3. Доказать: результат merge является перестановкой конкатенации входных списков.

-- 4. Определение функции merge_sort
-- 4.1. Реализовать merge_sort рекурсивно, используя split и merge.
-- 4.2. Указать меру уменьшения (обычно длина списка) для доказательства завершения.

-- 5. Доказательство корректности (главная теорема)
-- 5.3. База: длины 0 и 1 (тривиально).
-- 5.4. Шаг индукции:
-- 5.4.1. Разделить список l на l1 и l2 через split.
-- 5.4.2. Показать, что l1 и l2 короче l (используя п. 2.4).
-- 5.4.3. Применить индукционную гипотезу к l1 и l2.
-- 5.4.4. Получить, что merge_sort l1 и merge_sort l2 — отсортированы и являются перестановками l1 и l2 соответственно.
-- 5.4.5. Использовать свойство merge (п. 3.2) для сортированности.
-- 5.4.6. Использовать свойство merge (п. 3.3) и перестановочность split (п. 2.3),
-- чтобы получить перестановку исходного списка.
-- 6. (Опционально) Доказательство завершения (если не автоматическое)
-- 6.1. Показать, что каждый рекурсивный вызов merge_sort получает список строго меньшей длины.
-- 6.2. Сослаться на обоснованность натуральных чисел (или использовать well_founded).
-/

/-
1. Подготовительный этап
-/

variable (α : Type) [LinearOrder α] [DecidableEq α]
--для любых двух элементов a и b типа α (обладающего указанными свойствами) отношение a < b разрешимо
lemma decidableLT [LinearOrder α] [DecidableEq α] (a b : α) : Decidable (a < b) :=
  inferInstance
--трихотомия сравнения
lemma trichotomy [LinearOrder α] (a b : α) : a < b ∨ a = b ∨ b < a :=
  lt_trichotomy a b

/-
2. Определение вспомогательной функции halve
--(не использую "split" для избегания конфликта имен с list)
-/
def halve {α : Type} (xs : List α) : List α × List α :=
  let n := xs.length / 2
  (xs.take n, xs.drop n)

-- 2.2 Сумма длин частей равна длине исходного списка
lemma halve_length_sum {α : Type} (xs : List α) :
    let (left, right) := halve xs
    (left.length + right.length) = xs.length := by
  unfold halve
  simp [List.length_take, List.length_drop]
  rw [min_eq_left]
  · rw [Nat.add_sub_of_le]
    exact Nat.div_le_self (length xs) 2
  · exact Nat.div_le_self xs.length 2

-- 2.3 Конкатенация частей является перестановкой исходного списка
lemma halve_perm {α : Type} (xs : List α) :
    let (left, right) := halve xs
    Perm (left ++ right) xs := by
  unfold halve
  simp only
  let n := xs.length / 2
  rw [List.take_append_drop n xs]

-- 2.4 Уменьшение длины при непустом списке
lemma halve_length_lt {α : Type} (xs : List α) (h : 2 ≤ xs.length) :
    (halve xs).1.length < xs.length ∧ (halve xs).2.length < xs.length := by
  unfold halve
  simp
  constructor
  ·
    apply Nat.div_lt_self ?_ (by norm_num : 1 < 2)
    linarith
  ·
    have h_div_pos : 0 < length xs / 2 := Nat.div_pos (by linarith) (by norm_num : 0 < 2)
    exact Nat.sub_lt (by linarith : 0 < length xs) h_div_pos

/-
3. Определение функции merge
-/
def my_merge {α : Type} [LinearOrder α] : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x::xs, y::ys =>
    if x ≤ y then
      x :: my_merge xs (y::ys)
    else
      y :: my_merge (x::xs) ys

--3.2. Корректность сортировки результата merge

-- Подлемма 1: Для случая x ≤ y
lemma my_merge_sorted_case_le {α : Type} [LinearOrder α] (x y : α) (xs ys : List α)
    (hxy : x ≤ y)
    (hxs_sorted : List.Sorted (· ≤ ·) (x::xs))
    (hys_sorted : List.Sorted (· ≤ ·) (y::ys))
    (ih : ∀ (xs ys : List α), List.Sorted (· ≤ ·) xs → List.Sorted (· ≤ ·) ys →
          List.Sorted (· ≤ ·) (my_merge xs ys)) :
    List.Sorted (· ≤ ·) (x :: my_merge xs (y::ys)) := by
  -- Из hxs_sorted получаем, что x ≤ все элементы xs
  have hx_le_xs : ∀ z ∈ xs, x ≤ z := by
    cases hxs_sorted
    case nil =>
      -- Этот случай невозможен, так как x::xs не пустой список
      exfalso
      simp at hxs_sorted
    case rel h _ =>
      exact h

  -- Доказываем, что x ≤ все элементы my_merge xs (y::ys)
  have hx_le_merge : ∀ z ∈ my_merge xs (y::ys), x ≤ z := by
    induction xs generalizing y with
    | nil =>
      simp [my_merge]
      intro z hz
      simp at hz
      cases hz with
      | inl h_eq =>
        rw [h_eq]
        exact hxy
      | inr h_in =>
        -- z ∈ ys, используем отсортированность ys
        cases hys_sorted with
        | nil => contradiction
        | rel hy_le_ys h_ys_tail =>
          exact le_trans hxy (hy_le_ys z h_in)
    | cons x' xs' ih_xs =>
      simp [my_merge]
      by_cases h : x' ≤ y
      · -- случай x' ≤ y
        simp [h, my_merge]
        intro z hz
        simp at hz
        cases hz with
        | inl h_eq =>
          rw [h_eq]
          exact hx_le_xs x' (by simp)
        | inr h_in =>
          have hx_le_xs' : ∀ w ∈ xs', x ≤ w := by
            intro w hw
            apply hx_le_xs
            simp [hw]
          apply ih_xs y ys hxy hx_le_xs' hys_sorted
          assumption
      · -- случай ¬(x' ≤ y) (т.е. y < x')
        simp [h, my_merge]
        intro z hz
        simp at hz
        cases hz with
        | inl h_eq =>
          rw [h_eq]
          exact hxy
        | inr h_in =>
          -- z ∈ my_merge (x'::xs') ys
          -- Используем предположение, что y ≤ все элементы ys и x' ≥ y
          have hy_le_ys : ∀ w ∈ ys, y ≤ w := by
            cases hys_sorted with
            | nil => contradiction
            | rel hy_le _ => exact hy_le
          have h_y_le_all : ∀ w ∈ (x'::xs'), y ≤ w := by
            intro w hw
            cases hw with
            | inl h_eq =>
              rw [h_eq]
              exact le_of_not_ge h
            | inr h_in_xs' =>
              apply le_trans (le_of_not_ge h)
              exact hx_le_xs w (by simp [h_in_xs'])
          -- Здесь нужна дополнительная индукция по ys
          sorry

  -- Сортируем хвост по индукции
  have h_tail_sorted : List.Sorted (· ≤ ·) (my_merge xs (y::ys)) := by
    cases hxs_sorted with
    | nil => exact ih xs (y::ys) List.Sorted.nil hys_sorted
    | rel _ hxs_tail => exact ih xs (y::ys) hxs_tail hys_sorted

  exact List.Sorted.cons hx_le_merge h_tail_sorted

-- Подлемма 2: Для случая ¬(x ≤ y) (т.е. y < x)
lemma my_merge_sorted_case_gt {α : Type} [LinearOrder α] (x y : α) (xs ys : List α)
    (hxy : ¬ x ≤ y)
    (hxs_sorted : List.Sorted (· ≤ ·) (x::xs))
    (hys_sorted : List.Sorted (· ≤ ·) (y::ys))
    (ih : ∀ (xs ys : List α), List.Sorted (· ≤ ·) xs → List.Sorted (· ≤ ·) ys →
          List.Sorted (· ≤ ·) (my_merge xs ys)) :
    List.Sorted (· ≤ ·) (y :: my_merge (x::xs) ys) := by
  have hyx : y ≤ x := le_of_not_ge hxy

  -- Из hys_sorted получаем, что y ≤ все элементы ys
  have hy_le_ys : ∀ z ∈ ys, y ≤ z := by
    cases hys_sorted
    · simp
    · assumption

  -- Доказываем, что y ≤ все элементы my_merge (x::xs) ys
  have hy_le_merge : ∀ z ∈ my_merge (x::xs) ys, y ≤ z := by
    induction ys generalizing x with
    | nil =>
      simp [my_merge]
      intro z hz
      simp at hz
      rcases hz with (rfl | hz_xs)
      · exact hyx
      · -- z ∈ xs, используем hxs_sorted
        cases hxs_sorted with
        | nil => contradiction
        | cons hx_le_xs _ =>
          have hy_le_x : y ≤ x := hyx
          have hx_le_z := hx_le_xs z hz_xs
          exact le_trans hy_le_x hx_le_z
    | cons y' ys' ih_ys =>
      simp [my_merge]
      by_cases h : x ≤ y'
      · simp [h, my_merge]
        intro z hz
        simp at hz
        rcases hz with (rfl | hz_merge)
        · -- z = x
          exact hyx
        · -- z ∈ my_merge xs ys'
          sorry
      · simp [h, my_merge]
        intro z hz
        simp at hz
        rcases hz with (rfl | hz_merge)
        · -- z = y'
          apply hy_le_ys
          simp
        · -- z ∈ my_merge (x::xs) ys'
          sorry

  -- Сортируем хвост по индукции
  have h_tail_sorted : List.Sorted (· ≤ ·) (my_merge (x::xs) ys) := by
    cases hys_sorted with
    | nil => exact ih (x::xs) ys hxs_sorted List.Sorted.nil
    | cons _ hys_tail => exact ih (x::xs) ys hxs_sorted hys_tail

  exact List.Sorted.cons hy_le_merge h_tail_sorted


lemma my_merge_sorted {α : Type} [LinearOrder α] (xs ys : List α)
    (hxs : List.Sorted (· ≤ ·) xs) (hys : List.Sorted (· ≤ ·) ys) :
    List.Sorted (· ≤ ·) (my_merge xs ys) := by
  induction xs generalizing ys with
  | nil =>
    simp [my_merge]
    exact hys
  | cons x xs ih =>
    induction ys generalizing xs with
    | nil =>
      simp [my_merge]
      exact hxs
    | cons y ys ih_ys =>
      simp [my_merge]
      by_cases hxy : x ≤ y
      ·
        simp [hxy, my_merge]
        have hx_le_xs : ∀ z ∈ xs, x ≤ z := by
          match hxs with
          | List.Sorted.rel h _ => exact h
        have hx_le_merge : ∀ z ∈ my_merge xs (y::ys), x ≤ z := by
          induction xs generalizing y with
          | nil =>
            simp [my_merge]
            intro z hz
            cases hz with
            | inl h_eq =>
              rw [h_eq]
              exact hxy
            | inr h_in =>
              match hys with
              | List.Sorted.rel hy_le_ys _ =>
                exact le_trans hxy (hy_le_ys z h_in)
          | cons x' xs' ih_xs =>
            simp [my_merge]
            by_cases h : x' ≤ y
            · simp [h, my_merge]
              intro z hz
              cases hz with
              | inl h_eq =>
                rw [h_eq]
                exact hx_le_xs x' (by simp)
              | inr h_in =>
                have hx_le_xs' : ∀ w ∈ xs', x ≤ w := by
                  intro w hw
                  apply hx_le_xs
                  simp [hw]
                exact ih_xs y ys hxy hx_le_xs' hys h_in
            · simp [h, my_merge]
              intro z hz
              cases hz with
              | inl h_eq =>
                rw [h_eq]
                exact hxy
              | inr h_in =>
                -- Здесь z ∈ my_merge (x'::xs') ys
                -- Нужно показать, что x ≤ z, используя транзитивность
                have hy_le_x' : y ≤ x' := le_of_not_ge h
                have hx_le_x' : x ≤ x' := le_trans hxy hy_le_x'
                have hx_le_ys : ∀ w ∈ ys, x ≤ w := by
                  intro w hw
                  match hys with
                  | List.Sorted.rel hy_le_ys _ =>
                    exact le_trans hxy (hy_le_ys w hw)
                -- По индукционной гипотезе для ys
                sorry  -- Это требует дополнительной индукции, упростим

        -- Хвост отсортирован по индукции
        have h_tail_sorted : List.Sorted (· ≤ ·) (my_merge xs (y::ys)) :=
          ih xs (y::ys) (by match hxs with | List.Sorted.rel _ h => exact h) hys

        exact List.Sorted.rel hx_le_merge h_tail_sorted

      · -- Случай y < x (т.е. ¬(x ≤ y))
        simp [hxy, my_merge]

        -- Из hys получаем, что y ≤ все элементы ys
        have hy_le_ys : ∀ z ∈ ys, y ≤ z := by
          match hys with
          | List.Sorted.rel h _ => exact h

        -- Из hxy имеем y ≤ x
        have hy_le_x : y ≤ x := le_of_not_ge hxy

        -- Доказываем, что y ≤ все элементы my_merge (x::xs) ys
        have hy_le_merge : ∀ z ∈ my_merge (x::xs) ys, y ≤ z := by
          induction ys generalizing x with
          | nil =>
            simp [my_merge]
            intro z hz
            cases hz with
            | inl h_eq =>
              rw [h_eq]
              exact hy_le_x
            | inr h_in =>
              -- z ∈ xs
              match hxs with
              | List.Sorted.rel hx_le_xs _ =>
                exact le_trans hy_le_x (hx_le_xs z h_in)
          | cons y' ys' ih_ys' =>
            simp [my_merge]
            by_cases h : x ≤ y'
            · simp [h, my_merge]
              intro z hz
              cases hz with
              | inl h_eq =>
                rw [h_eq]
                exact hy_le_x
              | inr h_in =>
                have hy_le_ys' : ∀ w ∈ ys', y ≤ w := by
                  intro w hw
                  apply hy_le_ys
                  simp [hw]
                exact ih_ys' x hxy hy_le_ys' (by assumption) h_in
            · simp [h, my_merge]
              intro z hz
              cases hz with
              | inl h_eq =>
                rw [h_eq]
                exact hy_le_ys y' (by simp)
              | inr h_in =>
                -- z ∈ my_merge (x::xs) ys'
                have hy_le_ys' : ∀ w ∈ ys', y ≤ w := by
                  intro w hw
                  apply hy_le_ys
                  simp [hw]
                exact ih_ys' x hxy hy_le_ys' (by assumption) h_in

        -- Хвост отсортирован по индукции
        have h_tail_sorted : List.Sorted (· ≤ ·) (my_merge (x::xs) ys) :=
          ih_ys (x::xs) (fun _ _ => ih _ _) hxs (by match hys with | List.Sorted.rel _ h => exact h)

        exact List.Sorted.rel hy_le_merge h_tail_sorted

--3.3. Результат merge является перестановкой конкатенации

-- Лемма 1a: Случай когда x ≤ y
lemma my_merge_perm_case_le {α : Type} [LinearOrder α] (x y : α) (xs ys : List α)
    (hxy : x ≤ y) (ih : ∀ (ys : List α), Perm (my_merge xs ys) (xs ++ ys)) :
    Perm (my_merge (x::xs) (y::ys)) (x :: (xs ++ (y::ys))) := by
  simp [my_merge, hxy]
  exact ih (y :: ys)

-- Лемма 1b: Случай когда y < x
lemma my_merge_perm_case_gt {α : Type} [LinearOrder α] (x y : α) (xs ys : List α)
    (hxy : ¬ x ≤ y) :
    Perm (my_merge (x::xs) (y::ys)) (y :: my_merge (x::xs) ys) := by
  simp [my_merge, hxy]

lemma perm_cons_append {α : Type} (y : α) (xs ys : List α) :
    Perm (y :: (xs ++ ys)) (xs ++ (y :: ys)) := by
  induction xs generalizing y with
  | nil =>
    simp
  | cons x xs ih =>
    simp [List.cons_append]
    apply Perm.trans
    · apply Perm.swap
    · apply Perm.cons x
      exact ih y

-- Лемма 2: my_merge (x::xs) ys ~ (x::xs) ++ ys (вспомогательная)
lemma my_merge_aux {α : Type} [LinearOrder α] (x : α) (xs ys : List α)
    (ih : ∀ (ys : List α), Perm (my_merge xs ys) (xs ++ ys)) :
    Perm (my_merge (x::xs) ys) ((x::xs) ++ ys) := by
  induction ys generalizing x with
  | nil =>
    simp [my_merge]
  | cons y ys' ih_ys =>
    simp [my_merge]
    by_cases h : x ≤ y
    · simp [h, my_merge]
      exact ih (y :: ys')
    · simp [h, my_merge]
      refine Perm.trans (Perm.cons y (ih_ys x)) (perm_cons_append y (x::xs) ys')

lemma my_merge_perm {α : Type} [LinearOrder α] (xs ys : List α) :
    Perm (my_merge xs ys) (xs ++ ys) := by
  induction xs generalizing ys with
  | nil =>
    simp [my_merge]
  | cons x xs ih =>
    induction ys generalizing xs with
    | nil =>
      simp [my_merge]
    | cons y ys =>
      by_cases hxy : x ≤ y
      · -- Случай x ≤ y
        have h1 := my_merge_perm_case_le x y xs ys hxy ih
        simp at h1
        exact h1
      · -- Случай y < x
        have h1 : Perm (my_merge (x::xs) (y::ys)) (y :: my_merge (x::xs) ys) := by
          simp [my_merge, hxy]

        have h2 : Perm (my_merge (x::xs) ys) ((x::xs) ++ ys) :=
          my_merge_aux x xs ys ih

        have h3 : Perm (y :: my_merge (x::xs) ys) (y :: ((x::xs) ++ ys)) :=
          Perm.cons y h2

        have h4 : Perm (my_merge (x::xs) (y::ys)) (y :: ((x::xs) ++ ys)) :=
          Perm.trans h1 h3

        have h5 : Perm (y :: ((x::xs) ++ ys)) ((x::xs) ++ (y::ys)) :=
          perm_cons_append y (x::xs) ys

        exact Perm.trans h4 h5

/-
4. Определение функции merge_sort
-/
def my_merge_sort {α : Type} [LinearOrder α] (xs : List α) : List α :=
  match xs with
  | [] => []
  | [x] => [x]
  | _ =>
    let (left, right) := halve xs
    my_merge (my_merge_sort left) (my_merge_sort right)
decreasing_by
  sorry

/-
5. Доказательство корректности (главная теорема)
-- 5.3. База: длины 0 и 1 (тривиально).
-- 5.4. Шаг индукции:
-- 5.4.1. Разделить список l на l1 и l2 через split.
-- 5.4.2. Показать, что l1 и l2 короче l (используя п. 2.4).
-- 5.4.3. Применить индукционную гипотезу к l1 и l2.
-- 5.4.4. Получить, что merge_sort l1 и merge_sort l2 — отсортированы и являются перестановками l1 и l2 соответственно.
-- 5.4.5. Использовать свойство merge (п. 3.2) для сортированности.
-- 5.4.6. Использовать свойство merge (п. 3.3) и перестановочность split (п. 2.3),
-- чтобы получить перестановку исходного списка.
-/

-- 5.3. База: длины 0 и 1 (тривиально).
-- 5.3. База: длины 0 и 1 (тривиально).
lemma merge_sort_sorted_nil {α : Type} [LinearOrder α] :
    List.Sorted (· ≤ ·) (my_merge_sort ([] : List α)) :=
  by
    unfold my_merge_sort
    exact List.sorted_nil

lemma merge_sort_sorted_singleton {α : Type} [LinearOrder α] (x : α) :
    List.Sorted (· ≤ ·) (my_merge_sort [x]) :=
  by
    unfold my_merge_sort
    exact List.sorted_singleton x

lemma merge_sort_perm_nil {α : Type} [LinearOrder α] :
    Perm (my_merge_sort ([] : List α)) [] :=
  by
    unfold my_merge_sort
    exact Perm.refl []

lemma merge_sort_perm_singleton {α : Type} [LinearOrder α] (x : α) :
    Perm (my_merge_sort [x]) [x] :=
  by
    unfold my_merge_sort
    exact Perm.refl [x]

lemma merge_sort_sorted {α : Type} [LinearOrder α] (l : List α) :
    List.Sorted (· ≤ ·) (my_merge_sort l) := by
  induction l with
  | nil =>
    simp [my_merge_sort]
  | cons x xs =>
    cases xs with
    | nil =>
      simp [my_merge_sort]
    | cons y rest =>
      have h_len : 2 ≤ (x::y::rest).length := by simp_arith [List.length_cons]
      let (left, right) := halve (x::y::rest)
      have h_halve := halve_length_lt (x::y::rest) h_len
      have h_left_len : left.length < (x::y::rest).length := by
        change (halve (x::y::rest)).1.length < (x::y::rest).length
        exact h_halve.1
      have h_right_len : right.length < (x::y::rest).length := by
        change (halve (x::y::rest)).2.length < (x::y::rest).length
        exact h_halve.2

      have h_left_sorted := merge_sort_sorted left
      have h_right_sorted := merge_sort_sorted right

      exact my_merge_sorted (my_merge_sort left) (my_merge_sort right) h_left_sorted h_right_sorted

lemma merge_sort_perm {α : Type} [LinearOrder α] (l : List α) :
    Perm (my_merge_sort l) l := by
  induction l with
  | nil =>
    simp [my_merge_sort]
  | cons x xs =>
    cases xs with
    | nil =>
      simp [my_merge_sort]
    | cons y rest =>
      have h_len : 2 ≤ (x::y::rest).length := by simp_arith [List.length_cons]
      let (left, right) := halve (x::y::rest)
      have h_halve := halve_length_lt (x::y::rest) h_len
      have h_left_len : left.length < (x::y::rest).length := h_halve.1
      have h_right_len : right.length < (x::y::rest).length := h_halve.2

      have h_left_perm := merge_sort_perm left
      have h_right_perm := merge_sort_perm right

      have h_merge_perm := my_merge_perm (my_merge_sort left) (my_merge_sort right)

      apply Perm.trans h_merge_perm
      apply Perm.trans
      · apply Perm.append h_left_perm h_right_perm
      · exact halve_perm (x::y::rest)

-- 5.5. Соединить оба пункта → доказательство главной теоремы.
theorem merge_sort_correct {α : Type} [LinearOrder α] (l : List α) :
    List.Sorted (· ≤ ·) (my_merge_sort l) ∧ Perm (my_merge_sort l) l :=
  And.intro (merge_sort_sorted l) (merge_sort_perm l)
