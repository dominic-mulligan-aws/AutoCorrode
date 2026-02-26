# Task Planning

Use task-list tools for genuinely multi-step work. Do not create overhead for simple one-step requests.

## When to Use Task Lists
- Use task lists when work has dependencies, multiple files, or a staged verification process.
- Skip task lists for trivial read-only questions or single small edits.

## Mandatory Task Lifecycle Rules
<EXTREMELY_IMPORTANT>
When using task lists, you MUST follow these rules strictly:

1. **After completing a task's acceptance criteria, you MUST immediately call `task_list_done`** with the task ID. Do not proceed to other work without marking it done first.

2. **After calling `task_list_done`, you MUST call `task_list_next`** to retrieve the next pending task. This is not optional.

3. **Never leave tasks in "pending" state when their acceptance criteria are met.** Always mark them done or irrelevant.

4. **If a task becomes obsolete or out of scope, immediately call `task_list_irrelevant`** with the task ID. Do not leave it hanging in the pending state.

5. **At the end of any multi-task workflow, call `task_list_show`** to confirm all tasks are properly resolved (done or irrelevant).

6. **Use `task_list_next` as your primary navigation mechanism** between tasks. Do not jump ahead to new tasks without explicitly calling it.

Failure to follow these rules will result in lost work and incomplete task tracking.
</EXTREMELY_IMPORTANT>

## Task Quality Rules
- Each task must have:
  - a concrete objective,
  - a concise implementation description,
  - explicit acceptance criteria tied to observable outcomes (for example: “no PIDE errors”, “proof complete without sorry”).
- Keep tasks small enough to complete in one focused pass.

## Execution Discipline
1. Plan:
   - Create tasks with `task_list_add`.
   - Check coverage with `task_list_show`.
2. Execute:
   - Pull next work item via `task_list_next`.
   - Complete, verify, then mark with `task_list_done`.
3. Adapt:
   - Add newly discovered work as new tasks.
   - Mark obsolete tasks with `task_list_irrelevant`.

## Isabelle-Specific Acceptance Criteria
- Prefer acceptance criteria that include:
  - successful proof state progression (`execute_step` / `verify_proof`),
  - final diagnostic checks (`set_cursor_position` to EOF + `get_errors`),
  - maintainable proof shape (not only “works once”).

## Reporting
- After each completed task, summarize what changed and what remains.
- Keep progress reports factual and brief.
