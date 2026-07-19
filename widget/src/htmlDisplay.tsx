/* Adapted from ProofWidgets' Apache-2.0 licensed HtmlDisplay component. */
import * as React from 'react'
import {
  EnvPosContext,
  importWidgetModule,
  mapRpcError,
  useAsyncPersistent,
  useRpcSession,
} from '@leanprover/infoview'
import type { DocumentPosition, RpcSessionAtPos } from '@leanprover/infoview'

export type Html =
  | { element: [string, [string, unknown][], Html[]] }
  | { text: string }
  | { component: [string, string, Record<string, unknown>, Html[]] }

async function renderHtml(
  rpcSession: RpcSessionAtPos,
  position: DocumentPosition,
  html: Html,
): Promise<React.ReactElement> {
  if ('text' in html) return <>{html.text}</>

  if ('element' in html) {
    const [tag, attributeList, children] = html.element
    const attributes = Object.fromEntries(attributeList)
    const renderedChildren = await Promise.all(
      children.map(child => renderHtml(rpcSession, position, child)),
    )
    return React.createElement(tag, attributes, ...renderedChildren)
  }

  const [hash, exportName, props, children] = html.component
  const renderedChildren = await Promise.all(
    children.map(child => renderHtml(rpcSession, position, child)),
  )
  const module = await importWidgetModule(rpcSession, position, hash)
  if (!(exportName in module)) {
    throw new Error(`Module '${hash}' does not export '${exportName}'`)
  }
  return React.createElement(
    module[exportName],
    { ...props, pos: position },
    ...renderedChildren,
  )
}

export default function HtmlDisplay({ html }: { html: Html }): React.ReactElement {
  const rpcSession = useRpcSession()
  const position = React.useContext(EnvPosContext)!
  const state = useAsyncPersistent(
    () => renderHtml(rpcSession, position, html),
    [rpcSession, position, html],
  )

  if (state.state === 'resolved') return state.value
  if (state.state === 'rejected') {
    return <span className="red">{mapRpcError(state.error).message}</span>
  }
  return <></>
}
