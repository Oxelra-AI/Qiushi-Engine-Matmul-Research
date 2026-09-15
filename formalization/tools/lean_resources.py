"""Process-local resource settings inherited by Lean subprocesses."""

try:
    import resource
except ImportError:
    resource = None


MIN_STACK_BYTES = 256 * 1024 * 1024


def configure_process_stack():
    """Raise only this process's soft stack limit; call before starting workers.

    Return a JSON-ready before/after record. Platforms without RLIMIT_STACK
    return an unsupported record; insufficient hard limits fail explicitly.
    """
    record = {"supported": False, "minimum_bytes": MIN_STACK_BYTES,
              "before": None, "after": None, "changed": False}
    if resource is None or not hasattr(resource, "RLIMIT_STACK"):
        return dict(record, reason="resource.RLIMIT_STACK is unavailable")
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    before = {"soft": soft, "hard": hard}
    if soft != resource.RLIM_INFINITY and soft < MIN_STACK_BYTES:
        if hard != resource.RLIM_INFINITY and hard < MIN_STACK_BYTES:
            raise RuntimeError(
                f"RLIMIT_STACK hard limit {hard} bytes is below the required "
                f"{MIN_STACK_BYTES} bytes (256 MiB); cannot start Lean safely")
        try:
            resource.setrlimit(resource.RLIMIT_STACK, (MIN_STACK_BYTES, hard))
        except (OSError, ValueError) as error:
            raise RuntimeError(
                f"Cannot raise process RLIMIT_STACK soft limit from {soft} to "
                f"{MIN_STACK_BYTES} bytes while preserving hard limit {hard}: "
                f"{error}") from error
    after_soft, after_hard = resource.getrlimit(resource.RLIMIT_STACK)
    after = {"soft": after_soft, "hard": after_hard}
    return dict(record, supported=True, before=before, after=after,
                changed=before != after)
