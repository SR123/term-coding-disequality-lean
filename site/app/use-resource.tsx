'use client';
import {useEffect, useState} from 'react';
import {fetchResource, type ResourceFormat} from './resource-loader';

export type Resource<T> = {
  data: T | null;
  status: 'idle' | 'loading' | 'retrying' | 'ready' | 'error';
  retry: () => void;
};
// Only successful responses are retained. A failed request can always be tried again.
const cache = new Map<string, unknown>();

export function useResource<T>(url: string | null, format: ResourceFormat = 'json'): Resource<T> {
  const [revision, setRevision] = useState(0);
  const key = format + ':' + (url ?? '');
  const [state, setState] = useState<{key: string; revision: number; data: T | null; status: Resource<T>['status']}>({
    key: '', revision: -1, data: null, status: 'idle',
  });
  useEffect(() => {
    if (!url) return;
    const controller = new AbortController();
    const update = (status: Resource<T>['status'], data: T | null = null) => {
      if (!controller.signal.aborted) setState({key, revision, status, data});
    };
    if (cache.has(key)) {
      update('ready', cache.get(key) as T);
      return;
    }
    update('loading');
    fetchResource<T>(url, {
      format, signal: controller.signal, fresh: revision > 0,
      onRetry: () => update('retrying'),
    }).then(data => {
      if (controller.signal.aborted) return;
      cache.set(key, data);
      update('ready', data);
    }).catch(() => update('error'));
    return () => controller.abort();
  }, [url, format, key, revision]);
  const current = state.key === key && state.revision === revision;
  return {
    data: url && current ? state.data : null,
    status: !url ? 'idle' : current ? state.status : 'loading',
    retry: () => {
      cache.delete(key);
      setRevision(value => value + 1);
    },
  };
}

export function ResourceNotice({resource, label, retryLabel}: {
  resource: Pick<Resource<unknown>, 'status' | 'retry'>;
  label: string;
  retryLabel: string;
}) {
  if (resource.status === 'loading' || resource.status === 'retrying') {
    return <p role="status">{resource.status === 'retrying' ? `Still loading ${label}. Retrying automatically…` : `Loading ${label}…`}</p>;
  }
  if (resource.status !== 'error') return null;
  return <div className="resource-error">
    <p role="alert">We couldn’t load {label}. Your place in the paper is preserved.</p>
    <button type="button" onClick={resource.retry}>{retryLabel}</button>
    <a href="./paper/lean-source.zip" download>Download the full Lean source</a>
  </div>;
}
