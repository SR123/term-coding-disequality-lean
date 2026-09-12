export type ResourceFormat = 'json' | 'text';

class ResponseError extends Error {
  status: number;
  constructor(status: number) {
    super(`File request failed (${status}).`);
    this.status = status;
  }
}

function cancelled(signal?: AbortSignal) {
  if (signal?.aborted) throw signal.reason ?? new DOMException('Cancelled', 'AbortError');
}

function pause(ms: number, signal?: AbortSignal) {
  return new Promise<void>((resolve, reject) => {
    cancelled(signal);
    const stop = () => {
      clearTimeout(timer);
      signal?.removeEventListener('abort', stop);
      reject(signal?.reason ?? new DOMException('Cancelled', 'AbortError'));
    };
    const timer = setTimeout(() => {
      signal?.removeEventListener('abort', stop);
      resolve();
    }, ms);
    signal?.addEventListener('abort', stop, {once: true});
  });
}

/** Retry transient failures only; cancellation also stops response-body reads and backoff. */
export async function fetchResource<T>(url: string, options: {
  format?: ResourceFormat;
  signal?: AbortSignal;
  fresh?: boolean;
  onRetry?: () => void;
  timeoutMs?: number;
  delays?: readonly number[];
  fetcher?: typeof fetch;
} = {}): Promise<T> {
  const {format = 'json', signal, fresh = false, onRetry,
    timeoutMs = 20000, delays = [600, 1500], fetcher = fetch} = options;
  for (let attempt = 0; ; attempt++) {
    cancelled(signal);
    const controller = new AbortController();
    const stop = () => controller.abort(signal?.reason);
    signal?.addEventListener('abort', stop, {once: true});
    const timer = setTimeout(() => controller.abort(new DOMException('Request timed out', 'TimeoutError')), timeoutMs);
    let failure: unknown;
    try {
      const response = await fetcher(url, {
        signal: controller.signal,
        cache: fresh || attempt > 0 ? 'reload' : 'default',
      });
      if (!response.ok) throw new ResponseError(response.status);
      const data = format === 'text' ? await response.text() : await response.json();
      cancelled(signal);
      return data as T;
    } catch (error) {
      cancelled(signal);
      failure = error;
    } finally {
      clearTimeout(timer);
      signal?.removeEventListener('abort', stop);
    }
    const temporary = !(failure instanceof ResponseError) ||
      failure.status === 408 || failure.status === 429 || failure.status >= 500;
    if (!temporary || attempt >= delays.length) throw failure;
    onRetry?.();
    await pause(delays[attempt], signal);
  }
}
